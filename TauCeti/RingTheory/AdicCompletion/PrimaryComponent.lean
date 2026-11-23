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
* The completion construction used here is Mathlib's `AdicCompletion`, by Kenny Lau,
  Judith Ludwig, Christian Merten, and Jiedong Jiang.
-/

public section

open Function Submodule

namespace Ideal

/-- A finite module consisting of ideal-power torsion is complete for that ideal. -/
theorem isAdicComplete_of_primaryComponent_eq_top {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] [Module.Finite R M] {I : Ideal R}
    (h : I.primaryComponent M = ⊤) : IsAdicComplete I M := by
  obtain ⟨k, hk⟩ := I.exists_le_torsionBySet_pow_of_le_primaryComponent
    Module.Finite.fg_top h.ge
  have hkill : I ^ k • (⊤ : Submodule R M) = ⊥ := by
    apply eq_bot_iff.mpr
    refine Submodule.smul_le.mpr fun a ha x hx ↦ ?_
    rw [Submodule.mem_bot]
    exact (Submodule.mem_torsionBySet_iff _ _).mp (hk hx) ⟨a, ha⟩
  exact TauCeti.isAdicComplete_of_pow_smul_eq_bot hkill

/-- A finite ideal-power torsion submodule is complete for that ideal. -/
instance isAdicComplete_primaryComponent_of_finite {R M : Type*} [CommRing R]
    [AddCommGroup M] [Module R M] (I : Ideal R) [Module.Finite R (I.primaryComponent M)] :
    IsAdicComplete I (I.primaryComponent M) :=
  isAdicComplete_of_primaryComponent_eq_top I.primaryComponent_primaryComponent_eq_top

end Ideal

namespace AdicCompletion

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (r : R)

/-- If the parameter-power torsion of `M` is already complete, completion induces a
bijection on parameter-power torsion. The map is the restriction of the canonical completion
map, not an unspecified identification. -/
theorem primaryComponent_map_of_bijective_of_isAdicComplete
    [IsAdicComplete (Ideal.span {r}) ((Ideal.span {r}).primaryComponent M)] :
    Bijective (Ideal.primaryComponent.map (Ideal.span {r}) (of (Ideal.span {r}) M)) := by
  let I := Ideal.span {r}
  let T := I.primaryComponent M
  have hreg : IsSMulRegular (M ⧸ T) r :=
    (Ideal.primaryComponent_span_singleton_eq_bot_iff r).mp
      (Ideal.primaryComponent_quotient_primaryComponent
        (Submodule.fg_span (Set.finite_singleton r)))
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
      have hzero : I.primaryComponent (AdicCompletion I (M ⧸ T)) = ⊥ :=
        (Ideal.primaryComponent_span_singleton_eq_bot_iff r).mpr hreg.adicCompletion
      simpa only [hzero, Submodule.mem_bot, LinearMap.restrictScalars_apply] using hmem
    obtain ⟨z, hz⟩ := (hex (y : AdicCompletion I M)).mp hy
    obtain ⟨t, rfl⟩ := of_surjective I T z
    refine ⟨t, Subtype.ext ?_⟩
    simpa only [Ideal.primaryComponent.map_apply_coe, Submodule.subtype_apply] using
      (map_of I T.subtype t).symm.trans hz

/-- Bounded parameter-power torsion is unchanged by principal-adic completion. There are
no Noetherian or finite-generation hypotheses: only the torsion submodule must be killed by
a uniform power of the defining ideal. -/
theorem primaryComponent_map_of_bijective_of_pow_smul_eq_bot {k : ℕ}
    (hk : (Ideal.span {r}) ^ k •
      (⊤ : Submodule R ((Ideal.span {r}).primaryComponent M)) = ⊥) :
    Bijective (Ideal.primaryComponent.map (Ideal.span {r}) (of (Ideal.span {r}) M)) := by
  let := TauCeti.isAdicComplete_of_pow_smul_eq_bot hk
  exact primaryComponent_map_of_bijective_of_isAdicComplete r

/-- If the parameter-power torsion is complete, principal-adic completion identifies it with
the torsion of the completion. In particular this applies when the torsion submodule is finite.
The underlying map is induced by `AdicCompletion.of`. -/
noncomputable def primaryComponentEquiv
    [IsAdicComplete (Ideal.span {r}) ((Ideal.span {r}).primaryComponent M)] :
    (Ideal.span {r}).primaryComponent M ≃ₗ[R]
      (Ideal.span {r}).primaryComponent (AdicCompletion (Ideal.span {r}) M) :=
  LinearEquiv.ofBijective (Ideal.primaryComponent.map (Ideal.span {r})
    (of (Ideal.span {r}) M)) (primaryComponent_map_of_bijective_of_isAdicComplete r)

/-- The torsion comparison sends an element to its canonical image in the completion. -/
@[simp]
theorem coe_primaryComponentEquiv_apply
    [IsAdicComplete (Ideal.span {r}) ((Ideal.span {r}).primaryComponent M)]
    (x : (Ideal.span {r}).primaryComponent M) :
    (primaryComponentEquiv r x : AdicCompletion (Ideal.span {r}) M) =
      of (Ideal.span {r}) M (x : M) := by
  rw [primaryComponentEquiv, LinearEquiv.ofBijective_apply, Ideal.primaryComponent.map_apply_coe]

/-- Applying the canonical completion map to the inverse torsion comparison recovers the
original torsion element of the completion. -/
@[simp]
theorem of_coe_primaryComponentEquiv_symm_apply
    [IsAdicComplete (Ideal.span {r}) ((Ideal.span {r}).primaryComponent M)]
    (y : (Ideal.span {r}).primaryComponent (AdicCompletion (Ideal.span {r}) M)) :
    of (Ideal.span {r}) M ((primaryComponentEquiv r).symm y : M) = y := by
  rw [← coe_primaryComponentEquiv_apply, LinearEquiv.apply_symm_apply]

end AdicCompletion
