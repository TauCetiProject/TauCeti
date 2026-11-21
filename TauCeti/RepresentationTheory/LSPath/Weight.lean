/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.TensorProduct.Tower
public import TauCeti.RepresentationTheory.LSPath.Basic

import TauCeti.LinearAlgebra.RootSystem.BaseChange.Basic

/-!
# Lattice-valued endpoints of Lakshmibai–Seshadri paths

The endpoint of an LS path is a rational convex combination of orbit weights. Its break-chain
conditions imply more than integrality of its pairings: the endpoint is the image of a weight
in the original character lattice. This supplies the lattice-valued endpoints needed to equip LS
encodings with a crystal structure, including when the roots do not span the character lattice.

Summation by parts expresses the endpoint as the last orbit weight plus the sum of the
corrections `a_j (τ_{j-1} λ - τ_j λ)`. Each correction is the image of an integral root-lattice
vector, because each edge of its `a_j`-chain is a root multiplied by an integral coefficient.
Thus the endpoint differs from the last orbit weight by an actual root-lattice vector.
No injectivity or spanning assumption is needed for this existence result; injectivity of a
chosen realization then gives uniqueness of the lattice weight.

Using the canonical rational realization `M → ℚ ⊗[ℤ] M` (`RootPairing.tensorProduct_mk_injective`),
this yields the intrinsic lattice-valued weight `TauCeti.LSPath.weight`, characterized by its
endpoint image in every additive realization (`TauCeti.LSPath.apply_weight`,
`TauCeti.LSPath.weight_eq_iff_endpoint`, `TauCeti.LSPath.weight_eq_of_forall_endpoint_eq`).

## References

* P. Littelmann, *A Littlewood–Richardson rule for symmetrizable Kac–Moody algebras*, Invent.
  Math. 116 (1994), §4.
* P. Littelmann, *Paths and root operators in representation theory*, Ann. of Math. 142 (1995),
  §4.
-/

public section

namespace TauCeti.LSPath

open RootPairing

section Endpoint

variable {ι M N 𝕜 V : Type*} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced]
  {lam : M} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
  [AddCommGroup V] [Module 𝕜 V]

/-- Summation by parts for the endpoint of an LS path: the last orbit weight plus its
break-time-weighted changes of direction. -/
theorem endpoint_toPLPath_eq_last_add_sum (π : LSPath P b lam) (f : M →+ V) :
    (π.toPLPath 𝕜 f).endpoint = f ((π.dir (Fin.last _)).val • lam) +
      ∑ j : Fin π.length, (π.time j.castSucc.succ : 𝕜) •
        (f ((π.dir j.castSucc).val • lam) - f ((π.dir j.succ).val • lam)) := by
  rw [endpoint_toPLPath]
  simp only [duration_def, Rat.cast_sub, sub_smul, smul_sub, Finset.sum_sub_distrib]
  rw [Fin.sum_univ_castSucc (fun j : Fin (π.length + 1) ↦
    (π.time j.succ : 𝕜) • f ((π.dir j).val • lam)),
    Fin.sum_univ_succ (fun j : Fin (π.length + 1) ↦
      (π.time j.castSucc : 𝕜) • f ((π.dir j).val • lam))]
  simp only [Fin.succ_last, π.time_last, Rat.cast_one, one_smul, Fin.castSucc_zero,
    π.time_zero, Rat.cast_zero, zero_smul, zero_add, Fin.succ_castSucc]
  abel

/-- The endpoint of an LS path of dominant shape differs from its last orbit weight by the
image of an integral root-lattice vector. This is a lattice statement, not only integrality
of scalar pairings. -/
theorem exists_mem_rootSpan_endpoint_eq_add (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) :
    ∃ m ∈ P.rootSpan ℤ,
      (π.toPLPath 𝕜 f).endpoint = f ((π.dir (Fin.last _)).val • lam + m) := by
  classical
  have hcorrection (j : Fin π.length) : ∃ m ∈ P.rootSpan ℤ,
      (π.time j.castSucc.succ : 𝕜) •
        (f ((π.dir j.castSucc).val • lam) - f ((π.dir j.succ).val • lam)) = f m := by
    obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain j
    simpa only [hhead, hlast] using hC.exists_mem_rootSpan_smul_sub_eq hlam f
  choose m hm heq using hcorrection
  refine ⟨∑ j, m j, Submodule.sum_mem _ (fun j _ ↦ hm j), ?_⟩
  rw [π.endpoint_toPLPath_eq_last_add_sum f, map_add, map_sum]
  simp only [heq]

/-- Every realized LS endpoint is the image of a weight in the original lattice. When the
realization is injective, that weight is unique. -/
theorem existsUnique_endpoint_eq (π : LSPath P b lam)
    (hlam : lam ∈ dominantChamber P b) (f : M →+ V) (hf : Function.Injective f) :
    ∃! μ : M, (π.toPLPath 𝕜 f).endpoint = f μ := by
  obtain ⟨m, -, hm⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := 𝕜) hlam f
  exact ⟨_, hm, fun μ hμ ↦ hf (hμ.symm.trans hm)⟩

end Endpoint

/-! ### Canonical lattice-valued weight -/

section Weight

open scoped TensorProduct

universe u w x

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

/-- The canonical rational piecewise-linear realization of an LS path in `ℚ ⊗[ℤ] M`. -/
noncomputable abbrev toRatPLPath (π : LSPath P b lam) : PLPath ℚ (ℚ ⊗[ℤ] M) :=
  π.toPLPath ℚ (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom

/-- Pushing `LSPath.toRatPLPath` forward along the canonical semilinear extension of `f : M →+ V`
yields `π.toPLPath 𝕜 f`. -/
theorem mapSemilinear_toRatPLPath {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜]
    [IsStrictOrderedRing 𝕜] [AddCommGroup V] [Module 𝕜 V] (f : M →+ V) (π : LSPath P b lam) :
    π.toRatPLPath.mapSemilinear (f.liftBaseChangeSemilinear (Rat.castHom 𝕜)) =
      π.toPLPath 𝕜 f := by
  rw [toRatPLPath, mapSemilinear_toPLPath ℚ _ _ (Rat.cast_mono (K := 𝕜)),
    AddMonoidHom.liftBaseChangeSemilinear_comp_mk]

/-- **The lattice-valued weight of an LS path of dominant shape**, characterized by
`f (π.weight hlam) = (π.toPLPath 𝕜 f).endpoint` (`TauCeti.LSPath.apply_weight`). -/
noncomputable def weight (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) : M :=
  Classical.choose (π.existsUnique_endpoint_eq (𝕜 := ℚ) hlam
    (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom (P.tensorProduct_mk_injective ℚ))

/-- In every realization `(𝕜, V, f)`, `f (π.weight hlam)` is the endpoint of `π.toPLPath 𝕜 f`. -/
theorem apply_weight (𝕜 : Type*) {V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : M →+ V) (hlam : lam ∈ dominantChamber P b)
    (π : LSPath P b lam) : f (π.weight hlam) = (π.toPLPath 𝕜 f).endpoint := by
  have hrat : (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom (π.weight hlam) =
      π.toRatPLPath.endpoint :=
    (Classical.choose_spec (π.existsUnique_endpoint_eq (𝕜 := ℚ) hlam
      (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom (P.tensorProduct_mk_injective ℚ))).1.symm
  nth_rw 1 [← f.liftBaseChangeSemilinear_comp_mk (Rat.castHom 𝕜)]
  rw [AddMonoidHom.comp_apply, LinearMap.toAddMonoidHom_coe, hrat, ← PLPath.endpoint_mapSemilinear,
    mapSemilinear_toRatPLPath]

/-- Characterization of `π.weight hlam` by its endpoint in any injective realization `f : M →+ V`.
-/
theorem weight_eq_iff_endpoint {𝕜 V : Type*} [Field 𝕜] [LinearOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] {f : M →+ V} (hf : Function.Injective f)
    (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) {μ : M} :
    π.weight hlam = μ ↔ (π.toPLPath 𝕜 f).endpoint = f μ := by
  rw [← apply_weight 𝕜 f hlam π, hf.eq_iff]

/-- `π.weight hlam = μ` if `(π.toPLPath ℚ f).endpoint = f μ` for every rational realization `f`. -/
theorem weight_eq_of_forall_endpoint_eq (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam)
    {μ : M} (h : ∀ {V : Type w} [AddCommGroup V] [Module ℚ V] (f : M →+ V),
      (π.toPLPath ℚ f).endpoint = f μ) :
    π.weight hlam = μ :=
  (weight_eq_iff_endpoint (𝕜 := ℚ) (P.tensorProduct_mk_injective ℚ) hlam π).mpr
    (h (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom)

@[simp]
theorem weight_straight (hlam : lam ∈ dominantChamber P b) : (straight lam).weight hlam = lam :=
  weight_eq_of_forall_endpoint_eq hlam (straight lam) fun f ↦ by
    rw [toPLPath_straight, PLPath.endpoint_straight]

@[simp]
theorem weight_congr {lam' : M} (h : lam = lam') (hlam' : lam' ∈ dominantChamber P b)
    (π : LSPath P b lam) : (congr h π).weight hlam' = π.weight (h.symm ▸ hlam') := by
  subst h; simp

/-- The weight of an LS path differs from its last orbit weight `τ_l • λ` by a root-lattice element.
-/
theorem weight_sub_last_mem_rootSpan (hlam : lam ∈ dominantChamber P b) (π : LSPath P b lam) :
    π.weight hlam - (π.dir (Fin.last _)).val • lam ∈ P.rootSpan ℤ := by
  obtain ⟨m, hm, heq⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := ℚ) hlam
    (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom
  simpa [(weight_eq_iff_endpoint (𝕜 := ℚ) (P.tensorProduct_mk_injective ℚ) hlam π).mpr heq]
    using hm

end Weight

end TauCeti.LSPath
