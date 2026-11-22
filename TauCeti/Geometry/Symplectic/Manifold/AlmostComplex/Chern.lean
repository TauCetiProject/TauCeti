/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.PiL2
public import TauCeti.Geometry.Manifold.Complex.AlmostComplexStructure
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.ComplexTangentBundle
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Polar
public import TauCeti.Geometry.Symplectic.Manifold.AlmostComplex.Pullback
public import TauCeti.Topology.Homotopy.HomotopyGroup.BasepointChange
public import TauCeti.Topology.VectorBundle.Complex.RealStructure
public import TauCeti.Topology.VectorBundle.Complex.LinearPart
import TauCeti.Geometry.Manifold.VectorBundle.Tangent.RestrictScalars
import TauCeti.Geometry.Symplectic.Cayley.Basic
import TauCeti.Geometry.Symplectic.Finrank

/-!
# The first Chern number of a symplectic manifold on spheres

Let `σ` be a fiberwise nondegenerate two-form on a manifold `M`, for instance a symplectic form.
An almost complex structure `J` tamed by `σ` makes the tangent bundle a complex vector bundle
`(TM, J)`, and its clutching number on spheres is the first Chern number `c₁(TM, J)` on the second
homotopy group `π₂(M, x)` (`TauCeti.clutchingNumberHom`). This file shows that it does not depend
on `J`, and so defines the first Chern number of `σ` on spheres.

* **Independence of `J`.** If `J` and `K` are both tamed by `σ`, then `1 - K J` is invertible on
  every tangent space (`TauCeti.SmoothTwoForm.Tames.isUnit_one_sub_toEndomorphism_mul`, from the
  linear `TauCeti.SymplecticForm.Tames.isUnit_one_sub_mul`): a vector with
  `K (J v) = v` has `K v = -J v`, and `σ(v, K v) = -σ(v, J v)` cannot be positive together with
  `σ(v, J v)` unless `v = 0`. So the complex-linear part `v ↦ (v - K (J v)) / 2` of the identity is
  an isomorphism of complex vector bundles `(TM, J) ≃ (TM, K)`
  (`TauCeti.Bundle.ContinuousComplexStructure.complexLinearPartEquiv`), and the clutching numbers of
  `(TM, J)` and `(TM, K)` agree (`TauCeti.SmoothTwoForm.Tames.clutchingNumberHom_eq`), for any
  complex model fibres and any smoothness levels at which `J` and `K` are regarded.
* **The first Chern number of `σ`.** On a Hausdorff σ-compact manifold every fiberwise
  nondegenerate two-form has a compatible, in particular tame, smooth almost complex structure
  (`TauCeti.SmoothTwoForm.IsNondegenerate.exists_compatible`). The first Chern number of `σ` on
  `π₂(M, x)` (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom`) is the clutching number
  homomorphism of `(TM, J)` for one such `J`, with model fibre `ℂⁿ`, `2n = dim M`. By independence
  it is the clutching number homomorphism of `(TM, J)` for every tame `J` and every complex model
  fibre (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom`).
* **Independence of the base point.** Transporting a class of `π₂(M, x)` along a path from `x`
  to `y` does not change its first Chern number
  (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_homotopyGroupTransport`), because clutching
  numbers do not (`TauCeti.clutchingNumberHom_homotopyGroupTransport`). In particular the first
  Chern number is invariant under the action of the fundamental group on `π₂(M, x)`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_fundamentalGroup_smul`).
* **Symplectic and anti-symplectic diffeomorphisms.** If a diffeomorphism `h : M → N` pulls a
  nondegenerate two-form `σ'` back to `σ`, it carries the first Chern number of `σ` on a class
  `a ∈ π₂(M, x)` to that of `σ'` on `h_* a`
  (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_map_of_mpullback_eq`): for `J'` tamed by
  `σ'`, the pulled-back structure `h^* J'` is tamed by `σ` and the differential of `h` is a
  complex-linear isomorphism `(TM, h^* J') ≃ (TN, J')` covering `h`, so clutching numbers are
  preserved (`TauCeti.clutchingNumber_map_of_continuousLinearEquiv`). If instead `h^* σ' = -σ`,
  the structure `-h^* J'` is tamed by `σ` and the differential is conjugate linear, so the first
  Chern number changes sign
  (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_map_of_mpullback_eq_neg`, through
  `TauCeti.clutchingNumber_map_of_conjugateLinear`). Consequently, if an anti-symplectic
  diffeomorphism of `M` is homotopic to the identity, a sphere and its image have both the same
  and opposite first Chern numbers, so the first Chern number of `σ` vanishes
  (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_zero_of_mpullback_eq_neg`). The fibre
  negation of a cotangent bundle is such a map.
* **Complex manifolds.** On a complex manifold `M` modelled on `E`, if `σ` tames the complex
  structure `TauCeti.SmoothAlmostComplexStructure.ofComplexManifold E M`, multiplication by `i`,
  then the complex vector bundle `(TM, i)` is the holomorphic tangent bundle: the identity of `E`
  on the fibres is complex linear, and continuous on total spaces
  (`TangentBundle.restrictScalarsHomeomorph`). So the first Chern number of `σ` is the
  clutching number homomorphism of the holomorphic tangent bundle
  (`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom_tangentSpace`).

The first Chern number on spheres and the symplectic area of spheres
(`TauCeti.sphereIntegralHom`) are the two periods of capped Hamiltonian Floer theory: the grading
and the action of a capped periodic orbit change by `2 c₁(B)` and `ω(B)` when a sphere `B` is glued
to its cap. The first Chern number here is the clutching description on spheres; no comparison
with a cohomological first Chern class is made.

## Main definitions

* `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom`: the first Chern number
  `π₂(M, x) → ℤ` of a fiberwise nondegenerate two-form.

## Main results

* `TauCeti.SmoothTwoForm.Tames.clutchingNumberHom_eq`: two almost complex structures tamed by the
  same two-form give the same clutching numbers.
* `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom`: the first Chern
  number is the clutching number homomorphism of the tangent bundle for any tame almost complex
  structure.
* `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_homotopyGroupTransport`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_fundamentalGroup_smul`: the first Chern
  number does not depend on the base point.
* `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_map_of_mpullback_eq`,
  `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_map_of_mpullback_eq_neg`: symplectic
  diffeomorphisms preserve the first Chern number and anti-symplectic ones reverse it.
* `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_zero_of_mpullback_eq_neg`: an
  anti-symplectic diffeomorphism homotopic to the identity forces the first Chern number to vanish.
* `TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom_tangentSpace`: on a
  complex manifold, for a two-form taming the complex structure, it is the clutching number
  homomorphism of the holomorphic tangent bundle.

## References

* D. McDuff and D. Salamon, *Introduction to Symplectic Topology*, third edition, Oxford (2017),
  Section 2.6 (the space of tame complex structures and the first Chern class of a symplectic
  manifold) and Section 2.7 (the first Chern number of a symplectic bundle over a surface).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Appendix C.1 (the first Chern number of a bundle over a surface by clutching).
-/

public section

noncomputable section

open Bundle Module Topology
open scoped ContDiff Manifold Topology.Homotopy

namespace TauCeti.SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I ∞ M]
  {σ : SmoothTwoForm I M} {J K : SmoothAlmostComplexStructure I M}

variable [FiniteDimensional ℝ E]
  (G G' : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)] [NormedAddCommGroup G'] [NormedSpace ℂ G']
  [FiniteDimensional ℂ G'] [Fact (finrank ℝ E = 2 * finrank ℂ G')]

/-- **Independence of the tame almost complex structure.** If `J` and `K` are both tamed by `σ`,
the tangent bundles `(TM, J)` and `(TM, K)` have the same clutching number homomorphism
`π₂(M, x) → ℤ`, for any complex model fibres `G` and `G'` and any smoothness levels `n` and `m` at
which `J` and `K` are regarded. -/
theorem Tames.clutchingNumberHom_eq (hJ : σ.Tames J) (hK : σ.Tames K) (n m : ℕ∞) (x : M) :
    clutchingNumberHom G' (K.toContMDiff m).toContinuousComplexStructure.Fiber x =
      clutchingNumberHom G (J.toContMDiff n).toContinuousComplexStructure.Fiber x := by
  refine Bundle.ContinuousComplexStructure.clutchingNumberHom_fiber_eq (fun y v hv ↦ ?_) G G' x
  -- On each tangent space, `1 - K J` is invertible because `J` and `K` are tamed by `σ`.
  have hunit := hJ.isUnit_one_sub_toEndomorphism_mul hK y
  apply (ContinuousLinearEquiv.unitsEquiv ℝ _ hunit.unit).injective
  simpa [sub_eq_zero] using hv.symm

namespace IsNondegenerate

variable [T2Space M] [SigmaCompactSpace M]

/-- The model space `E` of a manifold with a fiberwise nondegenerate two-form has even dimension,
so `ℂⁿ` with `n = dim E / 2` is a complex model fibre for its tangent bundle. -/
private theorem two_mul_finrank_euclideanSpace (h : σ.IsNondegenerate) (x : M) :
    finrank ℝ E = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) := by
  rw [finrank_euclideanSpace_fin, Nat.two_mul_div_two_of_even]
  exact ((exists_compatible h).choose.almostComplexStructureAt x).even_finrank_real

/-- The **first Chern number** `c₁ : π₂(M, x) → ℤ` of a fiberwise nondegenerate two-form `σ` on a
Hausdorff σ-compact manifold: the clutching number homomorphism of the tangent bundle, made a
complex vector bundle by an almost complex structure compatible with `σ`. It does not depend on
that structure, nor on the complex model fibre: it is the clutching number homomorphism for every
almost complex structure tamed by `σ`
(`TauCeti.SmoothTwoForm.IsNondegenerate.firstChernHom_eq_clutchingNumberHom`). -/
def firstChernHom (h : σ.IsNondegenerate) (x : M) : Additive (π_ 2 M x) →+ ℤ :=
  haveI : Fact (finrank ℝ E = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))) :=
    ⟨two_mul_finrank_euclideanSpace h x⟩
  clutchingNumberHom (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))
    ((exists_compatible h).choose.toContMDiff ⊤).toContinuousComplexStructure.Fiber x

/-- **The first Chern number from any tame almost complex structure.** The first Chern number of
`σ` on `π₂(M, x)` is the clutching number homomorphism of the tangent bundle `(TM, J)`, for every
almost complex structure `J` tamed by `σ` and every complex model fibre `G`. -/
theorem firstChernHom_eq_clutchingNumberHom (h : σ.IsNondegenerate) (hJ : σ.Tames J) (n : ℕ∞)
    (x : M) :
    h.firstChernHom x =
      clutchingNumberHom G (J.toContMDiff n).toContinuousComplexStructure.Fiber x := by
  have : Fact (finrank ℝ E = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))) :=
    ⟨two_mul_finrank_euclideanSpace h x⟩
  exact Tames.clutchingNumberHom_eq _ _ hJ (exists_compatible h).choose_spec.tames n ⊤ x

/-- The first Chern number of `σ` on the class of a sphere `p` is the clutching number of `p` for
the tangent bundle `(TM, J)`, for every almost complex structure `J` tamed by `σ` and every
complex model fibre `G`. -/
theorem firstChernHom_apply_mk (h : σ.IsNondegenerate) (hJ : σ.Tames J) (n : ℕ∞) {x : M}
    (p : Ω^ (Fin 2) M x) :
    h.firstChernHom x (Additive.ofMul (Quotient.mk _ p)) =
      clutchingNumber G (J.toContMDiff n).toContinuousComplexStructure.Fiber p := by
  rw [firstChernHom_eq_clutchingNumberHom G h hJ n x, clutchingNumberHom_apply_mk]

/-- **Base-point change.** The first Chern number at `y`, on the transport of a class of `π₂(M, x)`
along a path from `x` to `y`, is the first Chern number at `x` on that class. -/
@[simp]
theorem firstChernHom_homotopyGroupTransport (h : σ.IsNondegenerate) {x y : M} (γ : Path x y)
    (a : π_ 2 M x) :
    h.firstChernHom y (Additive.ofMul (homotopyGroupTransport γ a)) =
      h.firstChernHom x (Additive.ofMul a) := by
  have : Fact (finrank ℝ E = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))) :=
    ⟨two_mul_finrank_euclideanSpace h x⟩
  have hJ := (exists_compatible h).choose_spec.tames
  rw [firstChernHom_eq_clutchingNumberHom (EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) h hJ ⊤ y,
    firstChernHom_eq_clutchingNumberHom (EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) h hJ ⊤ x,
    clutchingNumberHom_homotopyGroupTransport]

/-- The first Chern number is invariant under the action of the fundamental group on
`π₂(M, x)`. -/
theorem firstChernHom_fundamentalGroup_smul (h : σ.IsNondegenerate) {x : M}
    (g : FundamentalGroup M x) (a : π_ 2 M x) :
    h.firstChernHom x (Additive.ofMul (g • a)) = h.firstChernHom x (Additive.ofMul a) := by
  obtain ⟨p, hp⟩ := Path.Homotopic.Quotient.mk_surjective g.toPath
  rw [fundamentalGroup_smul_eq_transport hp.symm, firstChernHom_homotopyGroupTransport]

/-! ### Symplectic and anti-symplectic diffeomorphisms -/

section Diffeomorph

variable {E' H' N : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [FiniteDimensional ℝ E']
  [TopologicalSpace H'] {I' : ModelWithCorners ℝ E' H'} [TopologicalSpace N] [ChartedSpace H' N]
  [IsManifold I' ∞ N] {σ' : SmoothTwoForm I' N}

/-- The differential of a diffeomorphism `h : M → N` at `x`, as a complex-linear isomorphism from
the tangent space of `M` with the pulled-back complex structure `h^* J'` to the tangent space of
`N` with `J'`. -/
private def mfderivFiberEquiv (h : M ≃ₘ⟮I, I'⟯ N) (J' : SmoothAlmostComplexStructure I' N)
    (x : M) :
    ((J'.pullback h).toContMDiff ⊤).toContinuousComplexStructure.Fiber x ≃L[ℂ]
      (J'.toContMDiff ⊤).toContinuousComplexStructure.Fiber (h x) :=
  let K := ((J'.pullback h).toContMDiff ⊤).toContinuousComplexStructure
  let K' := (J'.toContMDiff ⊤).toContinuousComplexStructure
  let A := h.mfderivToContinuousLinearEquiv (by simp) x
  { toFun v := (K'.fiberEquiv (h x)).symm (A (K.fiberEquiv x v))
    invFun w := (K.fiberEquiv x).symm (A.symm (K'.fiberEquiv (h x) w))
    map_add' v w := by simp
    map_smul' z v := by
      apply (K'.fiberEquiv (h x)).injective
      simp only [RingHom.id_apply, Bundle.ContinuousComplexStructure.fiberEquiv_smul,
        ContinuousLinearEquiv.apply_symm_apply, map_add, map_smul]
      simp [K, K', A]
    left_inv v := by simp
    right_inv w := by simp
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

/-- The differential of a diffeomorphism `h : M → N` at `x`, as a conjugate-linear isomorphism from
the tangent space of `M` with the complex structure `-h^* J'` to the tangent space of `N` with
`J'`. -/
private def mfderivConjFiberEquiv (h : M ≃ₘ⟮I, I'⟯ N) (J' : SmoothAlmostComplexStructure I' N)
    (x : M) :
    ((-J'.pullback h).toContMDiff ⊤).toContinuousComplexStructure.Fiber x ≃L⋆[ℂ]
      (J'.toContMDiff ⊤).toContinuousComplexStructure.Fiber (h x) :=
  let K := ((-J'.pullback h).toContMDiff ⊤).toContinuousComplexStructure
  let K' := (J'.toContMDiff ⊤).toContinuousComplexStructure
  let A := h.mfderivToContinuousLinearEquiv (by simp) x
  { toFun v := (K'.fiberEquiv (h x)).symm (A (K.fiberEquiv x v))
    invFun w := (K.fiberEquiv x).symm (A.symm (K'.fiberEquiv (h x) w))
    map_add' v w := by simp
    map_smul' z v := by
      apply (K'.fiberEquiv (h x)).injective
      simp only [Bundle.ContinuousComplexStructure.fiberEquiv_smul,
        ContinuousLinearEquiv.apply_symm_apply, map_add, map_smul]
      simp [K, K', A, SmoothAlmostComplexStructure.mfderiv_pullback_apply]
    left_inv v := by simp
    right_inv w := by simp
    continuous_toFun := by fun_prop
    continuous_invFun := by fun_prop }

section Continuity

variable (G G' : Type*) [NormedAddCommGroup G] [NormedSpace ℂ G] [FiniteDimensional ℂ G]
  [Fact (finrank ℝ E = 2 * finrank ℂ G)] [NormedAddCommGroup G'] [NormedSpace ℂ G']
  [FiniteDimensional ℂ G'] [Fact (finrank ℝ E' = 2 * finrank ℂ G')]

omit [T2Space M] [SigmaCompactSpace M] in
/-- On total spaces, `mfderivFiberEquiv` is the tangent map of `h`, hence continuous. -/
private theorem continuous_mfderivFiberEquiv (h : M ≃ₘ⟮I, I'⟯ N)
    (J' : SmoothAlmostComplexStructure I' N) :
    Continuous fun v : TotalSpace G
        ((J'.pullback h).toContMDiff ⊤).toContinuousComplexStructure.Fiber ↦
      TotalSpace.mk' G' (h v.proj) (mfderivFiberEquiv h J' v.proj v.snd) := by
  refine (((J'.toContMDiff ⊤).toContinuousComplexStructure.totalSpaceHomeomorph
    G').symm.continuous.comp (h.contMDiff.continuous_tangentMap (by simp))).comp
      (((J'.pullback h).toContMDiff ⊤).toContinuousComplexStructure.totalSpaceHomeomorph
        G).continuous |>.congr fun v ↦ ?_
  simp [mfderivFiberEquiv, tangentMap]

omit [T2Space M] [SigmaCompactSpace M] in
/-- On total spaces, `mfderivConjFiberEquiv` is the tangent map of `h`, hence continuous. -/
private theorem continuous_mfderivConjFiberEquiv (h : M ≃ₘ⟮I, I'⟯ N)
    (J' : SmoothAlmostComplexStructure I' N) :
    Continuous fun v : TotalSpace G
        ((-J'.pullback h).toContMDiff ⊤).toContinuousComplexStructure.Fiber ↦
      TotalSpace.mk' G' (h v.proj) (mfderivConjFiberEquiv h J' v.proj v.snd) := by
  refine (((J'.toContMDiff ⊤).toContinuousComplexStructure.totalSpaceHomeomorph
    G').symm.continuous.comp (h.contMDiff.continuous_tangentMap (by simp))).comp
      (((-J'.pullback h).toContMDiff ⊤).toContinuousComplexStructure.totalSpaceHomeomorph
        G).continuous |>.congr fun v ↦ ?_
  simp [mfderivConjFiberEquiv, tangentMap]

end Continuity

variable [T2Space N] [SigmaCompactSpace N]

/-- **Symplectomorphisms preserve the first Chern number.** If a diffeomorphism `h : M → N` pulls
`σ'` back to `σ`, then the first Chern number of `σ'` on the image `h_* a ∈ π₂(N, h x)` of a class
`a ∈ π₂(M, x)` is the first Chern number of `σ` on `a`. -/
theorem firstChernHom_map_of_mpullback_eq (hσ : σ.IsNondegenerate) (hσ' : σ'.IsNondegenerate)
    (h : M ≃ₘ⟮I, I'⟯ N) (hh : SmoothForm.mpullback h h.contMDiff σ' = σ) (x : M)
    (a : π_ 2 M x) :
    hσ'.firstChernHom (h x) (.ofMul (HomotopyGroup.map ⟨h, h.continuous⟩ rfl a)) =
      hσ.firstChernHom x (.ofMul a) := by
  have : Fact (finrank ℝ E = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))) :=
    ⟨two_mul_finrank_euclideanSpace hσ x⟩
  have : Fact (finrank ℝ E' = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E' / 2)))) :=
    ⟨two_mul_finrank_euclideanSpace hσ' (h x)⟩
  obtain ⟨J', hJ'⟩ := exists_compatible hσ'
  have hJ : σ.Tames (J'.pullback h) := hh ▸ hJ'.tames.pullback h
  rw [hσ'.firstChernHom_eq_clutchingNumberHom (EuclideanSpace ℂ (Fin (finrank ℝ E' / 2)))
      hJ'.tames ⊤,
    hσ.firstChernHom_eq_clutchingNumberHom (EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) hJ ⊤]
  exact clutchingNumberHom_map_of_continuousLinearEquiv ⟨h, h.continuous⟩ (mfderivFiberEquiv h J')
    (continuous_mfderivFiberEquiv _ _ h J') rfl a

/-- **Anti-symplectic diffeomorphisms reverse the first Chern number.** If a diffeomorphism
`h : M → N` pulls `σ'` back to `-σ`, then the first Chern number of `σ'` on the image
`h_* a ∈ π₂(N, h x)` of a class `a ∈ π₂(M, x)` is the negative of the first Chern number of `σ`
on `a`. Indeed `-h^* J'` is tamed by `σ` whenever `J'` is tamed by `σ'`, and the differential of
`h` is conjugate linear from `-h^* J'` to `J'`. -/
theorem firstChernHom_map_of_mpullback_eq_neg (hσ : σ.IsNondegenerate)
    (hσ' : σ'.IsNondegenerate) (h : M ≃ₘ⟮I, I'⟯ N)
    (hh : SmoothForm.mpullback h h.contMDiff σ' = -σ) (x : M) (a : π_ 2 M x) :
    hσ'.firstChernHom (h x) (.ofMul (HomotopyGroup.map ⟨h, h.continuous⟩ rfl a)) =
      -hσ.firstChernHom x (.ofMul a) := by
  have : Fact (finrank ℝ E = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))) :=
    ⟨two_mul_finrank_euclideanSpace hσ x⟩
  have : Fact (finrank ℝ E' = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E' / 2)))) :=
    ⟨two_mul_finrank_euclideanSpace hσ' (h x)⟩
  obtain ⟨J', hJ'⟩ := exists_compatible hσ'
  have hJ : σ.Tames (-J'.pullback h) := by
    have hJh := hJ'.tames.pullback h
    rw [hh, SmoothTwoForm.tames_iff] at hJh
    refine SmoothTwoForm.tames_iff.2 fun y v hv ↦ ?_
    have hy := hJh y v hv
    rw [SmoothBundleForm.eval₂_neg] at hy
    -- `tames_iff` states the goal through the redex `(fun x ↦ ⇑((-h^* J').toEndomorphism x)) y v`;
    -- restate it as the application `(-h^* J') y v` that `neg_apply` rewrites.
    change 0 < SmoothBundleForm.eval₂ σ y v ((-J'.pullback h) y v)
    rw [SmoothAlmostComplexStructure.neg_apply, SmoothBundleForm.eval₂_neg_right]
    linarith
  rw [hσ'.firstChernHom_eq_clutchingNumberHom (EuclideanSpace ℂ (Fin (finrank ℝ E' / 2)))
      hJ'.tames ⊤,
    hσ.firstChernHom_eq_clutchingNumberHom (EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) hJ ⊤]
  exact clutchingNumberHom_map_of_conjugateLinear ⟨h, h.continuous⟩ (mfderivConjFiberEquiv h J')
    (continuous_mfderivConjFiberEquiv _ _ h J') rfl a

end Diffeomorph

/-- **An anti-symplectic diffeomorphism homotopic to the identity kills the first Chern number.**
If a diffeomorphism `h` of `M` pulls `σ` back to `-σ` and is homotopic to the identity, then the
first Chern number of `σ` vanishes on `π₂(M, x)` for every `x`. A sphere `p` and its image `h ∘ p`
have the same first Chern number, since the homotopy moves one into the other through spheres, and
opposite first Chern numbers, since `h` is anti-symplectic. -/
theorem firstChernHom_eq_zero_of_mpullback_eq_neg (hσ : σ.IsNondegenerate) (h : M ≃ₘ⟮I, I⟯ M)
    (hh : SmoothForm.mpullback h h.contMDiff σ = -σ)
    (H : (ContinuousMap.id M).Homotopy ⟨h, h.continuous⟩) (x : M) : hσ.firstChernHom x = 0 := by
  have : Fact (finrank ℝ E = 2 * finrank ℂ (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))) :=
    ⟨two_mul_finrank_euclideanSpace hσ x⟩
  obtain ⟨J, hJ⟩ := exists_compatible hσ
  refine AddMonoidHom.ext fun a ↦ ?_
  induction a using Additive.rec with
  | ofMul a =>
    induction a using Quotient.inductionOn with
    | h p =>
      have hneg := hσ.firstChernHom_map_of_mpullback_eq_neg hσ h hh x ⟦p⟧
      rw [HomotopyGroup.map_mk, firstChernHom_apply_mk (EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) hσ
        hJ.tames ⊤, firstChernHom_apply_mk (EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) hσ
        hJ.tames ⊤] at hneg
      have hhom := clutchingNumber_eq_of_homotopyAlong
        (F := EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))
        (E := (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber) (GenLoop.HomotopyAlong.map H p)
      rw [GenLoop.map_id] at hhom
      rw [firstChernHom_apply_mk (EuclideanSpace ℂ (Fin (finrank ℝ E / 2))) hσ hJ.tames ⊤,
        AddMonoidHom.zero_apply]
      -- `hhom` is stated at the base point `ContinuousMap.id M x` and `hneg` at `x`, which agree
      -- by definition; ascribing the type at `x` lets `omega` see one atom.
      have hp : clutchingNumber (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))
          (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber p =
            -clutchingNumber (EuclideanSpace ℂ (Fin (finrank ℝ E / 2)))
              (J.toContMDiff ⊤).toContinuousComplexStructure.Fiber p :=
        hhom.symm.trans hneg
      omega

end IsNondegenerate

end TauCeti.SmoothTwoForm

/-! ### Complex manifolds -/

namespace TauCeti.SmoothTwoForm.IsNondegenerate

open SmoothAlmostComplexStructure
open scoped TauCeti.ComplexManifold

variable {E M : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E]
  [TopologicalSpace M] [ChartedSpace E M] [IsManifold 𝓘(ℂ, E) ∞ M]

/-- The real dimension of a complex normed space is twice its complex dimension, so `E` is a
complex model fibre for the tangent bundle of a complex manifold modelled on `E`. -/
private local instance : Fact (finrank ℝ E = 2 * finrank ℂ E) := ⟨finrank_real_of_complex E⟩

/-- On a complex manifold, the fibre of the real tangent bundle with the complex structure `i` is
the fibre of the holomorphic tangent bundle, by the identity of `E`. -/
private def holomorphicTangentEquiv (n : ℕ∞) (x : M) :
    ((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.Fiber x ≃L[ℂ]
      TangentSpace 𝓘(ℂ, E) x :=
  let J := ((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure
  { toFun v := (J.fiberEquiv x v : E)
    invFun v := (J.fiberEquiv x).symm v
    map_add' := map_add (J.fiberEquiv x)
    map_smul' z v := by
      -- In the fibre `z • v = re z • v + im z • J v`, and `J` is multiplication by `i` on `E`.
      set w : E := J.fiberEquiv x v
      have hJ : J x w = Complex.I • w :=
        ((ContMDiffAlmostComplexStructure.toContinuousComplexStructure_apply _ x w).trans
          (toContMDiff_apply _ n x w)).trans (ofComplexManifold_apply x w)
      exact (J.fiberEquiv_smul x z v).trans
        ((congrArg (z.re • w + z.im • ·) hJ).trans (Complex.re_smul_add_im_smul z w))
    left_inv v := (J.fiberEquiv x).symm_apply_apply v
    right_inv v := (J.fiberEquiv x).apply_symm_apply v
    continuous_toFun := (J.fiberEquiv x).continuous
    continuous_invFun := (J.fiberEquiv x).symm.continuous }

private theorem holomorphicTangentEquiv_apply (n : ℕ∞) (x : M)
    (v : ((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.Fiber x) :
    holomorphicTangentEquiv n x v =
      (((ofComplexManifold E M).toContMDiff n).toContinuousComplexStructure.fiberEquiv x v : E) :=
  (rfl)

variable [FiniteDimensional ℂ E] [T2Space M] [SigmaCompactSpace M]

/-- **The first Chern number of a complex manifold.** If a fiberwise nondegenerate two-form `σ` on
a complex manifold `M` tames its complex structure (multiplication by `i` on the tangent spaces),
for instance a Kähler form, then its first Chern number on `π₂(M, x)` is the clutching number
homomorphism of the holomorphic tangent bundle of `M`. -/
theorem firstChernHom_eq_clutchingNumberHom_tangentSpace {σ : SmoothTwoForm 𝓘(ℝ, E) M}
    (h : σ.IsNondegenerate) (hJ : σ.Tames (ofComplexManifold E M)) (x : M) :
    h.firstChernHom x = clutchingNumberHom E (TangentSpace 𝓘(ℂ, E)) x := by
  set J := ((ofComplexManifold E M).toContMDiff ⊤).toContinuousComplexStructure
  rw [h.firstChernHom_eq_clutchingNumberHom E hJ ⊤ x]
  refine (clutchingNumberHom_eq_of_continuousLinearEquiv (holomorphicTangentEquiv ⊤) ?_ x).symm
  -- On total spaces the identification is the identity of the real tangent bundle, followed by
  -- the identity from the real onto the holomorphic tangent bundle.
  refine ((TangentBundle.restrictScalarsHomeomorph ℝ (𝕜' := ℂ) M).symm.continuous.comp
    (J.totalSpaceHomeomorph E).continuous).congr fun v ↦ ?_
  rw [Function.comp_apply, Bundle.ContinuousComplexStructure.totalSpaceHomeomorph_apply,
    TangentBundle.restrictScalarsHomeomorph_symm_apply, holomorphicTangentEquiv_apply]
  -- The identifications `tangentSpaceCastModel` of tangent spaces with `E` are the identity by
  -- definition, and Mathlib states no evaluation lemma for them.
  rfl

end TauCeti.SmoothTwoForm.IsNondegenerate
