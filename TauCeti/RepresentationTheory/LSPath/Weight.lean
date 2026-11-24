/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.RepresentationTheory.LSPath.Realization.Basic

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
this yields the intrinsic lattice-valued weight `TauCeti.LSPath.weight`, which maps to the
endpoint in every additive realization (`TauCeti.LSPath.apply_weight`) and is uniquely characterized
by the endpoint in the canonical rational realization
(`TauCeti.LSPath.weight_eq_iff_endpoint_toRatPLPath`) or in any injective realization
(`TauCeti.LSPath.weight_eq_iff_endpoint`).

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
  {lam : M} [Field 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
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

/-- The endpoint of an LS path differs from its last orbit weight by the image of an integral
root-lattice vector. This is a lattice statement, not only integrality of scalar pairings. -/
theorem exists_mem_rootSpan_endpoint_eq_add (π : LSPath P b lam) (f : M →+ V) :
    ∃ m ∈ P.rootSpan ℤ,
      (π.toPLPath 𝕜 f).endpoint = f ((π.dir (Fin.last _)).val • lam + m) := by
  classical
  have hcorrection (j : Fin π.length) : ∃ m ∈ P.rootSpan ℤ,
      (π.time j.castSucc.succ : 𝕜) •
        (f ((π.dir j.castSucc).val • lam) - f ((π.dir j.succ).val • lam)) = f m := by
    obtain ⟨C, hhead, hlast, hC⟩ := π.exists_isAChain j
    simpa only [hhead, hlast] using hC.exists_mem_rootSpan_smul_sub_eq f
  choose m hm heq using hcorrection
  refine ⟨∑ j, m j, Submodule.sum_mem _ (fun j _ ↦ hm j), ?_⟩
  rw [π.endpoint_toPLPath_eq_last_add_sum f, map_add, map_sum]
  simp only [heq]

/-- Every realized LS endpoint is the image of a weight in the original lattice. When the
realization is injective, that weight is unique. -/
theorem existsUnique_endpoint_eq (π : LSPath P b lam) (f : M →+ V) (hf : Function.Injective f) :
    ∃! μ : M, (π.toPLPath 𝕜 f).endpoint = f μ := by
  obtain ⟨m, -, hm⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := 𝕜) f
  exact ⟨_, hm, fun μ hμ ↦ hf (hμ.symm.trans hm)⟩

end Endpoint

/-! ### Canonical lattice-valued weight -/

section Weight

open scoped TensorProduct

universe u w x

variable {ι : Type u} {M : Type w} {N : Type x} [AddCommGroup M] [AddCommGroup N]
  {P : RootPairing ι ℤ M N} {b : P.Base} [Finite ι] [P.IsReduced] {lam : M}

/-- **The lattice-valued weight of an LS path**, sent to the endpoint in every additive realization
(`TauCeti.LSPath.apply_weight`) and uniquely characterized by the endpoint in any injective
realization (`TauCeti.LSPath.weight_eq_iff_endpoint`) or in the canonical rational realization
(`TauCeti.LSPath.weight_eq_iff_endpoint_toRatPLPath`). -/
noncomputable def weight (π : LSPath P b lam) : M :=
  Classical.choose (π.existsUnique_endpoint_eq (𝕜 := ℚ)
    (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom (P.tensorProduct_mk_injective ℚ))

/-- The canonical rational endpoint of `π` is the image of `π.weight`. -/
@[simp]
theorem endpoint_toRatPLPath (π : LSPath P b lam) :
    π.toRatPLPath.endpoint = TensorProduct.mk ℤ ℚ M 1 π.weight := by
  rw [toRatPLPath_def]
  exact (Classical.choose_spec (π.existsUnique_endpoint_eq (𝕜 := ℚ)
    (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom (P.tensorProduct_mk_injective ℚ))).1

/-- In every realization `(𝕜, V, f)`, `f π.weight` is the endpoint of `π.toPLPath 𝕜 f`. -/
theorem apply_weight (𝕜 : Type*) {V : Type*} [Field 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] (f : M →+ V) (π : LSPath P b lam) :
    f π.weight = (π.toPLPath 𝕜 f).endpoint := by
  calc f π.weight
      = (f.liftBaseChangeSemilinear (Rat.castHom 𝕜)) (TensorProduct.mk ℤ ℚ M 1 π.weight) :=
        (f.liftBaseChangeSemilinear_mk_one (Rat.castHom 𝕜) π.weight).symm
    _ = (f.liftBaseChangeSemilinear (Rat.castHom 𝕜)) π.toRatPLPath.endpoint :=
        congrArg _ π.endpoint_toRatPLPath.symm
    _ = (π.toPLPath 𝕜 f).endpoint := by
        rw [toRatPLPath_def, endpoint_toPLPath, endpoint_toPLPath, LinearMap.toAddMonoidHom_coe,
          map_sum]
        refine Finset.sum_congr rfl fun j _ ↦ ?_
        rw [map_smulₛₗ, AddMonoidHom.liftBaseChangeSemilinear_mk_one, Rat.coe_castHom, Rat.cast_id]

/-- Characterization of `π.weight` by its endpoint in any injective realization `f : M →+ V`. -/
theorem weight_eq_iff_endpoint {𝕜 V : Type*} [Field 𝕜] [PartialOrder 𝕜] [IsStrictOrderedRing 𝕜]
    [AddCommGroup V] [Module 𝕜 V] {f : M →+ V} (hf : Function.Injective f) (π : LSPath P b lam)
    {μ : M} : π.weight = μ ↔ (π.toPLPath 𝕜 f).endpoint = f μ := by
  rw [← apply_weight 𝕜 f π, hf.eq_iff]

/-- Characterization of `π.weight` by the endpoint of its canonical rational realization
`π.toRatPLPath`. -/
theorem weight_eq_iff_endpoint_toRatPLPath (π : LSPath P b lam) {μ : M} :
    π.weight = μ ↔ π.toRatPLPath.endpoint = TensorProduct.mk ℤ ℚ M 1 μ := by
  rw [toRatPLPath_def]
  exact weight_eq_iff_endpoint (𝕜 := ℚ) (P.tensorProduct_mk_injective ℚ) π

@[simp]
theorem weight_straight : (straight lam : LSPath P b lam).weight = lam :=
  (weight_eq_iff_endpoint_toRatPLPath (straight lam)).mpr (by
    rw [toRatPLPath_straight, PLPath.endpoint_straight])

@[simp]
theorem weight_congr {lam' : M} (h : lam = lam') (π : LSPath P b lam) :
    (congr h π).weight = π.weight := by
  subst h; simp

/-- The weight of an LS path differs from its last orbit weight `τ_l • λ` by a root-lattice element.
-/
theorem weight_sub_last_mem_rootSpan (π : LSPath P b lam) :
    π.weight - (π.dir (Fin.last _)).val • lam ∈ P.rootSpan ℤ := by
  obtain ⟨m, hm, heq⟩ := π.exists_mem_rootSpan_endpoint_eq_add (𝕜 := ℚ)
    (TensorProduct.mk ℤ ℚ M 1).toAddMonoidHom
  simpa [(weight_eq_iff_endpoint (𝕜 := ℚ) (P.tensorProduct_mk_injective ℚ) π).mpr heq] using hm

end Weight

end TauCeti.LSPath
