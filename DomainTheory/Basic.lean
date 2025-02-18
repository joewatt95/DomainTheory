import Loogle.Find

import Mathlib.Topology.Order.ScottTopology
import Mathlib.SetTheory.Ordinal.FixedPointApproximants

open Ordinal OrdinalApprox OmegaCompletePartialOrder OrderHom

instance [inst : CompleteLattice α] : Lean.Order.CCPO α :=
  let {le, le_refl, le_trans, le_antisymm, sSup, le_sSup, sSup_le, ..} := inst
  { rel := le
    rel_refl := le_refl _
    rel_trans := le_trans _ _ _
    rel_antisymm := le_antisymm _ _
    csup := sSup
    csup_spec {x c} _ :=
      { mp h' y (_ : c y) :=
          have : le y <| sSup c := le_sSup _ _ ‹c y›
          show le y x from le_trans _ _ _ this h'
        mpr := sSup_le _ _ }
  }

variable
  [CompleteLattice α] {f : α →o α}
  (omega_continuous : ωScottContinuous f)

-- Sanity check.
example [CompleteLattice β] {f : α → β} :
  Monotone f ↔ Lean.Order.monotone f := .rfl

lemma lfpApprox_add_one_eq :
  ∀ ord, lfpApprox f ⊥ (ord + 1) = f (lfpApprox f ⊥ ord) :=
  lfpApprox_add_one _ _ <| OrderBot.bot_le _

lemma lfpApprox_ofNat_eq_Nat_iterate :
  ∀ {n : ℕ}, lfpApprox f ⊥ n = f^[n] ⊥
  | 0 => by unfold lfpApprox; simp
  | n + 1 => calc
      lfpApprox f ⊥ (n + 1)
  _ = f (lfpApprox f ⊥ n)  := lfpApprox_add_one_eq _
  _ = f (f^[n] ⊥)          := by rw [lfpApprox_ofNat_eq_Nat_iterate]
  _ = f^[n + 1] ⊥          := by rw [Function.iterate_succ_apply']

lemma lfp_eq_lfpApprox_ord_of_fixed_point
  (_ : f (lfpApprox f ⊥ ord) = lfpApprox f ⊥ ord) :
  lfp f = lfpApprox f ⊥ ord :=
  have ⟨ord', (_ : lfpApprox f ⊥ ord' = lfp f)⟩ :=
    OrdinalApprox.lfp_mem_range_lfpApprox f

  calc
      lfp f
  _ = lfpApprox f ⊥ ord' := Eq.symm ‹_›
  _ = lfpApprox f ⊥ ord :=
    have :
      (ord' ≤ ord → lfpApprox f ⊥ ord = lfpApprox f ⊥ ord') ∧
      (ord' ≥ ord → lfpApprox f ⊥ ord' = lfpApprox f ⊥ ord) := by
      refine ⟨?_, ?_⟩
      repeat
        intro
        apply lfpApprox_eq_of_mem_fixedPoints
        . exact OrderBot.bot_le _
        . assumption
        . simp_all only [Function.mem_fixedPoints, Function.IsFixedPt, map_lfp]

    match le_total _ _ with
    | .inl (_ : ord' ≤ ord) | .inr (_ : ord' ≥ ord) =>
      by simp_all only [map_lfp, forall_const, ge_iff_le]

-- This proof is annoying as we need to juggle casting between `ℕ` and `Ordinal`
lemma lfpApprox_omega0_eq_sSup_lfpApprox_Nat :
  lfpApprox f ⊥ ω = ⨆ n : ℕ, lfpApprox f ⊥ n :=
  Eq.symm <| calc
      sSup {lfpApprox f ⊥ n | n : ℕ}

  _ = sSup {a | a = lfpApprox f ⊥ 0 ∨ ∃ n : ℕ, a = lfpApprox f ⊥ (n + 1)} :=
    congr_arg _ <| Set.ext λ _ ↦ by
      simp only [Set.mem_setOf_eq, Nat.cast_add, Nat.cast_one, add_one_eq_succ]
      rw [←Nat.or_exists_add_one]
      aesop

  _ = sSup ({lfpApprox f ⊥ 0} ∪ {f <| lfpApprox f ⊥ n | n : ℕ}) :=
    congr_arg _ <|
      have := lfpApprox_add_one_eq (f := f)
      by aesop

  _ = sSup {f <| lfpApprox f ⊥ n | n : ℕ} :=
    have := calc
          lfpApprox f ⊥ 0
        ≤ lfpApprox f ⊥ 1     := lfpApprox_monotone _ _ <| Ordinal.zero_le _
      _ = f (lfpApprox f ⊥ 0) := by rw [←lfpApprox_add_one_eq, zero_add]

    have : lfpApprox f ⊥ 0 ≤ sSup {f <| lfpApprox f ⊥ n | n : ℕ} :=
      le_sSup_of_le ⟨0, by simp only [Nat.cast_zero]⟩ this

    by simp_all only [add_one_eq_succ, Set.singleton_union, sSup_insert, sup_of_le_right]

  _ = lfpApprox f ⊥ ω := by
    conv => rhs; unfold lfpApprox
    aesop (add unsafe congr) (add norm lt_omega0)

theorem fix_eq_order_lfp :
  Lean.Order.fix f f.monotone' = lfp f :=
  have : Lean.Order.fix f f.monotone' ≤ lfp f :=
    -- Transfinite induction over fixpoint iteration sequence, because that's
    -- the only proof rule the Lean compiler has for its domain theoretic
    -- fixpoint constructions.
    Lean.Order.fix_induct (motive := (. ≤ _)) (hf := f.monotone')
      -- Successor stage
      (h := λ x (h : x ≤ lfp f) ↦ calc
        f x ≤ f (lfp f) := by exact f.monotone' h
          _ = lfp f     := map_lfp _)
      -- Limit stage
      (hadm := by
        unfold Lean.Order.admissible
        intros
        -- Why does aesop refuse to apply sSup_le even when marked as a safe
        -- intro rule?
        -- Does it have issues resolving the typeclass hierarchy?
        apply sSup_le
        aesop)

  have : OrderHom.lfp f ≤ Lean.Order.fix f f.monotone' :=
    -- RHS is a fixed point of f
    f |>.monotone' |> Lean.Order.fix_eq |>.symm
    -- Hence it upper bounds the least fixed point of f
      |> OrderHom.lfp_le_fixed _

  le_antisymm ‹_› ‹_›

-- The fixpoint combinator as used in the Lean compiler is denotationally equal
-- to the transfinite iteration over ordinals up to the Hartog number of the
-- underlying domain.
lemma fix_mem_range_lfpApprox :
  Lean.Order.fix f f.monotone' =
    lfpApprox f ⊥ (Order.succ <| Cardinal.mk α).ord :=
  let ord := (Order.succ <| Cardinal.mk α).ord
  have : lfpApprox f ⊥ ord = lfp f := lfpApprox_ord_eq_lfp _
  by simp_all only [fix_eq_order_lfp, ord]

-- Kleene fixpoint theorem, via fixed point iteration over `Ordinal` up to `ω`
-- as opposed to `ℕ`.
include omega_continuous in
theorem kleene_fixed_point :
  lfp f = lfpApprox f ⊥ ω :=
  let lfpApprox_Nat : Nat →o α :=
    { toFun := lfpApprox f ⊥ ∘ λ n : ℕ ↦ (n : Ordinal)
      monotone' := by aesop
        (add unsafe [Monotone.comp, Nat.mono_cast, lfpApprox_monotone]) }

  have : f (⨆ n, lfpApprox_Nat n) = ⨆ n, f (lfpApprox_Nat n) := by
    simp_all only [
      ωScottContinuous_iff_map_ωSup_of_orderHom, Chain, ωSup, Chain.map,
      comp_coe, Function.comp_apply]

  lfp_eq_lfpApprox_ord_of_fixed_point <| calc
        f (lfpApprox f ⊥ ω)

    _ = f (⨆ n : ℕ, lfpApprox f ⊥ n) := by rw [lfpApprox_omega0_eq_sSup_lfpApprox_Nat]

    _ = ⨆ n : ℕ, f (lfpApprox f ⊥ n) := by
      simp_all only [coe_mk, Function.comp_apply, lfpApprox_Nat]

    _ = ⨆ n : ℕ, lfpApprox f ⊥ (n + 1) :=
      have := lfpApprox_add_one_eq (f := f)
      by simp_all only [add_one_eq_succ, lfpApprox_Nat]

    _ = ⨆ n : ℕ, lfpApprox f ⊥ n :=
      le_antisymm
        (sSup_le_sSup λ _ ⟨n, _⟩ ↦ ⟨n + 1, by simp_all only [add_one_eq_succ, Set.mem_range, Nat.cast_add, Nat.cast_one]⟩) <|
        sSup_le_sSup_of_forall_exists_le λ a ⟨n, h⟩ ↦ by
          simp_all only [Set.mem_range, add_one_eq_succ, exists_exists_eq_and]
          exact ⟨n, by rw [←h]; apply lfpApprox_monotone; exact Order.le_succ _⟩

    _ = lfpApprox f ⊥ ω := by rw [lfpApprox_omega0_eq_sSup_lfpApprox_Nat]

-- TODO: Fixpoint induction iff transfinite induction over ordinals.
-- Formalise as transformation of proof?
