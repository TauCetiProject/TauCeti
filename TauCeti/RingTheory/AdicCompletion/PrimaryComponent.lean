/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Module.Torsion.PrimaryComponent
public import TauCeti.RingTheory.AdicCompletion.Exactness
public import TauCeti.RingTheory.AdicCompletion.Nilpotent
public import TauCeti.RingTheory.AdicCompletion.Regular

/-!
# Parameter-power torsion and principal-adic completion

Let `T` be the submodule of elements killed by a power of `r` in an `R`-module `M`.
If `T` is complete for `(r)`, the canonical map to the completion identifies `T` with the
parameter-power torsion of the completion of `M`. In particular this holds when a single
power of `r` kills `T`, and hence when `M` is Noetherian. Neither completeness of `R` nor
separatedness of `M` is required.

The quotient `M / T` is `r`-torsion-free, so its completion is also `r`-torsion-free.
Exactness of completion of `0 → T → M → M / T → 0` then identifies all the torsion in the
completed module. This permits removing bounded parameter-power torsion in comparisons of
ordinary completions with formal sections.

## References

* The Stacks Project, Lemma 52.3.2 (0BLD), cohomology and completion with stabilized
  parameter-power torsion, and Lemma 52.12.7 (0EII), formal sections.
* The completion construction used here is Mathlib's `AdicCompletion`, by Judith Ludwig
  and Christian Merten.
-/

public section

open Function Submodule

namespace AdicCompletion

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (r : R)

/-- If the parameter-power torsion of `M` is already complete, completion induces a
bijection on parameter-power torsion. The map is the restriction of the canonical completion
map, not an unspecified identification. -/
theorem bijective_primaryComponent_map_of_isAdicComplete
    [IsAdicComplete (Ideal.span {r}) ((Ideal.span {r}).primaryComponent M)] :
    Bijective (Ideal.primaryComponent.map (Ideal.span {r}) (of (Ideal.span {r}) M)) := by
  let I := Ideal.span {r}
  let T := I.primaryComponent M
  have hreg : IsSMulRegular (M ⧸ T) r := by
    apply (isSMulRegular_iff_torsionBy_eq_bot _ _).mpr
    apply le_antisymm ?_ bot_le
    intro x hx
    apply (Ideal.primaryComponent_quotient_primaryComponent
      (Submodule.fg_span (Set.finite_singleton r))).le
    simpa only [Finset.coe_singleton] using
      (Ideal.mem_primaryComponent_span_iff {r}).mpr (by
      intro s hs
      have hs' : s = r := by simpa using hs
      subst s
      exact ⟨1, by simpa using hx⟩)
  have hex := map_span_singleton_exact_of_isSMulRegular
    (LinearMap.exact_subtype_mkQ T) T.mkQ_surjective hreg
  have hinj := map_span_singleton_injective_of_isSMulRegular
    T.injective_subtype (LinearMap.exact_subtype_mkQ T) hreg
  constructor
  · intro x y hxy
    apply of_injective I T
    apply hinj
    have h := congrArg Subtype.val hxy
    rw [map_of, map_of]
    simpa only [Ideal.primaryComponent.map_apply_coe, Submodule.subtype_apply] using h
  · intro y
    have hy : map I T.mkQ (y : AdicCompletion I M) = 0 := by
      have hmem := I.primaryComponent_map_mem ((map I T.mkQ).restrictScalars R) y
      have hzero : I.primaryComponent (AdicCompletion I (M ⧸ T)) = ⊥ := by
        apply le_antisymm ?_ bot_le
        intro z hz
        have hz' : z ∈ (Ideal.span (↑({r} : Finset R) : Set R)).primaryComponent
            (AdicCompletion I (M ⧸ T)) := by
          simpa only [Finset.coe_singleton] using hz
        obtain ⟨n, hn⟩ := (Ideal.mem_primaryComponent_span_iff {r}).mp hz' r (by simp)
        exact (hreg.adicCompletion.pow n) (hn.trans (smul_zero _).symm)
      simpa only [hzero, Submodule.mem_bot, LinearMap.restrictScalars_apply] using hmem
    obtain ⟨z, hz⟩ := (hex (y : AdicCompletion I M)).mp hy
    obtain ⟨t, rfl⟩ := of_surjective I T z
    refine ⟨t, Subtype.ext ?_⟩
    exact (map_of I T.subtype t).symm.trans hz

/-- Bounded parameter-power torsion is unchanged by principal-adic completion. There are
no Noetherian or finite-generation hypotheses: only the torsion submodule must be killed by
a uniform power of the defining ideal. -/
theorem bijective_primaryComponent_map_of_pow_smul_eq_bot {k : ℕ}
    (hk : (Ideal.span {r}) ^ k •
      (⊤ : Submodule R ((Ideal.span {r}).primaryComponent M)) = ⊥) :
    Bijective (Ideal.primaryComponent.map (Ideal.span {r}) (of (Ideal.span {r}) M)) := by
  let := TauCeti.isAdicComplete_of_pow_smul_eq_bot hk
  exact bijective_primaryComponent_map_of_isAdicComplete r

/-- If the parameter-power torsion is finite, principal-adic completion identifies it with
the torsion of the completion. In particular this applies to Noetherian modules.
The underlying map is induced by `AdicCompletion.of`. -/
noncomputable def primaryComponentEquiv
    [Module.Finite R ((Ideal.span {r}).primaryComponent M)] :
    (Ideal.span {r}).primaryComponent M ≃ₗ[R]
      (Ideal.span {r}).primaryComponent (AdicCompletion (Ideal.span {r}) M) := by
  refine LinearEquiv.ofBijective (Ideal.primaryComponent.map (Ideal.span {r})
    (of (Ideal.span {r}) M)) ?_
  let I := Ideal.span {r}
  obtain ⟨k, hk⟩ := I.exists_le_torsionBySet_pow_of_le_primaryComponent
    (P := I.primaryComponent M) (Module.Finite.iff_fg.mp inferInstance) le_rfl
  have hkill : I ^ k • (⊤ : Submodule R (I.primaryComponent M)) = ⊥ := by
    apply eq_bot_iff.mpr
    refine Submodule.smul_le.mpr fun a ha x _ ↦ ?_
    apply Subtype.ext
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hk x.2) ⟨a, ha⟩
  exact bijective_primaryComponent_map_of_pow_smul_eq_bot r hkill

/-- The torsion comparison sends an element to its canonical image in the completion. -/
@[simp]
theorem coe_primaryComponentEquiv_apply
    [Module.Finite R ((Ideal.span {r}).primaryComponent M)]
    (x : (Ideal.span {r}).primaryComponent M) :
    (primaryComponentEquiv r x : AdicCompletion (Ideal.span {r}) M) =
      of (Ideal.span {r}) M (x : M) := by
  rfl

/-- Applying the canonical completion map to the inverse torsion comparison recovers the
original torsion element of the completion. -/
@[simp]
theorem of_coe_primaryComponentEquiv_symm_apply
    [Module.Finite R ((Ideal.span {r}).primaryComponent M)]
    (y : (Ideal.span {r}).primaryComponent (AdicCompletion (Ideal.span {r}) M)) :
    of (Ideal.span {r}) M ((primaryComponentEquiv r).symm y : M) = y := by
  rw [← coe_primaryComponentEquiv_apply, LinearEquiv.apply_symm_apply]

end AdicCompletion
