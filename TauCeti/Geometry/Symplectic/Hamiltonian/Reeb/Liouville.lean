/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Hamiltonian.Reeb.Basic
import TauCeti.Geometry.Contact.Reeb
import TauCeti.Geometry.Symplectic.Liouville.ContactType

/-!
# The sign of the Reeb field on a hypersurface transverse to a Liouville field

Let `σ` be a nondegenerate two-form on a finite-dimensional manifold `M`, with a primitive
`dα = σ` and a vector field `Z` contracting to it, `ι_Z σ = α`. This is the convention of
`TauCeti.IsContactType` and of the Liouville collar
(`TauCeti.exists_continuous_pos_partialDiffeomorph_flowOf_comp`), which pulls `α` back to
`eᵗ ι^* α`. In the convention `σ = -dλ`, `ι_Z σ = -λ` of exact symplectic manifolds, such as the
cotangent bundle with its Liouville form `λ = p dq`, the primitive is `α = -λ`; in Floer-theoretic
conventions it is written `λ_D` with `σ = dλ_D` and `ι_Z σ = λ_D`. So `λ_D = α = -λ`, and the
contact form of a hypersurface `ι : S → M` transverse to `Z` is `ι^* α = -ι^* λ`. On the unit
cosphere bundle this is the form `α_b = -λ|S*M`.

This file determines the direction of the Reeb field of this contact form relative to the
characteristic flow of the hypersurface. Let the tangent images of `ι` be the kernels of `dK`
for a function `K`, so that `X_K` spans the characteristic line, in the convention `ι_(X_K) σ = dK`.
Since `α(X_K) = σ(Z, X_K) = -dK(Z)`
(`TauCeti.SmoothTwoForm.IsNondegenerate.apply_hamiltonianVectorField_of_interior_eq`), the
rescaling `θ(X_K)⁻¹ X_K` of
`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback`, applied to `θ = -α`,
is explicit:

`dι (R_(ι^* α)) = -(dK(Z))⁻¹ • X_K`, `dι (R_(-ι^* α)) = (dK(Z))⁻¹ • X_K`

(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback_of_interior_eq`,
`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback_neg_of_interior_eq`),
where `dK(Z) ≠ 0` as soon as `ι^* α` is a contact form
(`TauCeti.SmoothTwoForm.IsNondegenerate.mvfderiv_apply_ne_zero_of_interior_eq`). When `Z` points
towards increasing `K`, as the outward Liouville field does at the boundary `{K = c}` of a
sublevel set `{K ≤ c}`, so that `dK(Z) > 0`, the Reeb field of `ι^* α = λ_D|S` is a negative
multiple of `X_K`: its flow runs backwards along the Hamiltonian flow of the outward defining
function, while the Reeb field of the opposite form `ι^* λ = -λ_D|S` runs forwards. Replacing the
primitive `λ_D` by `λ` keeps the contact hyperplanes and reverses the coorientation and the Reeb
field.

For a hypersurface whose transversality is stated through `K`, by `dK(Z) ≠ 0` along `ι`, the
restriction `ι^* α` is a contact form and the formula holds at every point
(`TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback_of_mvfderiv_ne_zero`).

On the unit cosphere bundle, with `K` the kinetic energy and `Z = p ∂_p` the radial field,
`dK(Z) = 1`. The formulas specialize to `R_(α_g) = X_K` and `R_(α_b) = -X_K`, the cogeodesic field
and its reverse (`TauCeti.CotangentBundle.mfderiv_coe_reebVectorField_cosphereBundle`,
`TauCeti.CotangentBundle.mfderiv_coe_reebVectorField_neg_cosphereBundle`). On a level
`r = e^t` of the cylindrical end of a Liouville completion, with `K = r` and `dr(Z) = r`, the
restricted primitive has Reeb field `-X_r / r`; this is the rescaled form of
`TauCeti.IsLiouvilleCompletion.mfderiv_flowOf_comp_reebVectorField`, by which the Liouville flow
carries the Reeb field of the boundary form to `-X_r`.

## Main results

* `TauCeti.SmoothTwoForm.IsNondegenerate.mvfderiv_apply_ne_zero_of_interior_eq`: on a
  hypersurface of contact type, `dK(Z) ≠ 0`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback_of_interior_eq`: the
  Reeb field of `ι^* α` is carried to `-(dK(Z))⁻¹ • X_K`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback_neg_of_interior_eq`:
  the Reeb field of `-ι^* α` is carried to `(dK(Z))⁻¹ • X_K`.
* `TauCeti.SmoothTwoForm.IsNondegenerate.mfderiv_reebVectorField_mpullback_of_mvfderiv_ne_zero`:
  the same formula for a hypersurface transverse to a Liouville field, with contactness derived.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type and their characteristic line fields).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.2 (the primitive `-λ` of the
  canonical form and the boundary of the unit codisc bundle).
-/

public section

open scoped ContDiff Manifold

namespace TauCeti

namespace SmoothTwoForm

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [TopologicalSpace H] {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I ∞ M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E']
  [TopologicalSpace H'] {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {σ : SmoothTwoForm I M}

variable [IsManifold J 2 S]

/-- `(-α)(X_K) = dK(z)` where `ι_z σ = α`. -/
private theorem neg_apply_hamiltonianVectorField_of_interior_eq (hσ : σ.IsNondegenerate)
    {α : SmoothForm I M ℝ 1} {x : M} {z : TangentSpace I x}
    (hzα : ∀ v, σ.val x ![z, v] = α.val x ![v]) (K : M → ℝ) :
    (-α).val x ![σ.hamiltonianVectorField K x] = mvfderiv I K x z := by
  rw [Submodule.coe_neg, Pi.neg_apply, ContinuousAlternatingMap.neg_apply,
    hσ.apply_hamiltonianVectorField_of_interior_eq hzα, neg_neg]

/-- **A Liouville vector is transverse to a hypersurface of contact type.** Let `σ = dα` at `ι s`
be nondegenerate and let `z` be a tangent vector with `ι_z σ = α` at `ι s`, such as the value of
a Liouville field of `α`. If the tangent image of `ι : S → M` at `s` is the kernel of `dK` and
the restriction `ι^* α` is a contact form, then `dK(z) ≠ 0`: the vector `z` is not tangent to
the hypersurface. -/
theorem IsNondegenerate.mvfderiv_apply_ne_zero_of_interior_eq (hσ : σ.IsNondegenerate)
    {α : SmoothForm I M ℝ 1} {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι α).IsContactForm) {K : M → ℝ} {s : S}
    (hdα : mextDeriv α.val (ι s) = σ.val (ι s)) {z : TangentSpace I (ι s)}
    (hzα : ∀ v, σ.val (ι s) ![z, v] = α.val (ι s) ![v])
    (hK : (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) :
    mvfderiv I K (ι s) z ≠ 0 := by
  rw [← neg_apply_hamiltonianVectorField_of_interior_eq hσ hzα]
  exact hσ.apply_hamiltonianVectorField_ne_zero hι
    ((SmoothForm.isContactForm_mpullback_neg_iff hι α).2 hα)
    (by rw [Submodule.coe_neg, mextDeriv_neg, Pi.neg_apply, hdα]) hK

/-- **The Reeb field of the opposite boundary form runs along the Hamiltonian flow.** Let
`σ = dα` at `ι s` be nondegenerate and let `z` be a tangent vector with `ι_z σ = α` at `ι s`,
such as the value of a Liouville field of `α`. If the tangent image of `ι : S → M` at `s` is the
kernel of `dK` and the restriction `ι^* α` is a contact form, then the differential of `ι` sends
the Reeb vector field of `-ι^* α` to `(dK(z))⁻¹ • X_K`.

In the convention `σ = -dλ`, `ι_z σ = -λ`, this is the Reeb field of `ι^* λ`. -/
theorem IsNondegenerate.mfderiv_reebVectorField_mpullback_neg_of_interior_eq
    (hσ : σ.IsNondegenerate) {α : SmoothForm I M ℝ 1} {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι α).IsContactForm) {K : M → ℝ} {s : S}
    (hdα : mextDeriv α.val (ι s) = σ.val (ι s)) {z : TangentSpace I (ι s)}
    (hzα : ∀ v, σ.val (ι s) ![z, v] = α.val (ι s) ![v])
    (hK : (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) :
    mfderiv J I ι s ((SmoothForm.mpullback ι hι (-α)).reebVectorField s) =
      (mvfderiv I K (ι s) z)⁻¹ • σ.hamiltonianVectorField K (ι s) := by
  rw [hσ.mfderiv_reebVectorField_mpullback hι
    ((SmoothForm.isContactForm_mpullback_neg_iff hι α).2 hα)
    (by rw [Submodule.coe_neg, mextDeriv_neg, Pi.neg_apply, hdα]) hK,
    neg_apply_hamiltonianVectorField_of_interior_eq hσ hzα]

/-- **The Reeb field of a hypersurface transverse to a Liouville field runs against the
Hamiltonian flow.** Let `σ = dα` at `ι s` be nondegenerate and let `z` be a tangent vector with
`ι_z σ = α` at `ι s`, such as the value of a Liouville field of `α`. If the tangent image of
`ι : S → M` at `s` is the kernel of `dK` and the restriction `ι^* α` is a contact form, then the
differential of `ι` sends the Reeb vector field of `ι^* α` to `-(dK(z))⁻¹ • X_K`.

So where `dK(z) > 0`, as for the outward Liouville field on the boundary of `{K ≤ c}`, the Reeb
field of `ι^* α` is a negative multiple of `X_K`. In the convention `σ = -dλ`, `ι_z σ = -λ`, this
is the Reeb field of `-ι^* λ`. -/
theorem IsNondegenerate.mfderiv_reebVectorField_mpullback_of_interior_eq
    (hσ : σ.IsNondegenerate) {α : SmoothForm I M ℝ 1} {ι : S → M} (hι : ContMDiff J I ∞ ι)
    (hα : (SmoothForm.mpullback ι hι α).IsContactForm) {K : M → ℝ} {s : S}
    (hdα : mextDeriv α.val (ι s) = σ.val (ι s)) {z : TangentSpace I (ι s)}
    (hzα : ∀ v, σ.val (ι s) ![z, v] = α.val (ι s) ![v])
    (hK : (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker) :
    mfderiv J I ι s ((SmoothForm.mpullback ι hι α).reebVectorField s) =
      -(mvfderiv I K (ι s) z)⁻¹ • σ.hamiltonianVectorField K (ι s) := by
  have h := hσ.mfderiv_reebVectorField_mpullback_neg_of_interior_eq hι hα hdα hzα hK
  rw [map_neg, hα.reebVectorField_neg, map_neg] at h
  rw [neg_smul, ← h, neg_neg]

/-- **The Reeb field of a hypersurface transverse to a Liouville field.** Let `σ` be a
nondegenerate two-form with primitive `α`, `dα = σ` along `ι`, and let `Z` be a vector field with
`ι_Z σ = α` along `ι`, such as a Liouville field of `α`. Let `ι : S → M` be a smooth map with
injective differentials from a manifold of one dimension less, whose tangent images are the
kernels of `dK`, and suppose `Z` is transverse to it, `dK(Z) ≠ 0` along `ι`. Then `ι^* α` is a
contact form (`TauCeti.SmoothTwoForm.IsNondegenerate.isContactForm_mpullback_of_interior_eq`),
and the differential of `ι` sends its Reeb vector field to `-(dK(Z))⁻¹ • X_K`. -/
theorem IsNondegenerate.mfderiv_reebVectorField_mpullback_of_mvfderiv_ne_zero
    (hσ : σ.IsNondegenerate) {α : SmoothForm I M ℝ 1} {Z : (x : M) → TangentSpace I x}
    {ι : S → M} (hι : ContMDiff J I ∞ ι) (hιs : ∀ s, Function.Injective (mfderiv J I ι s))
    (hdim : Module.finrank ℝ E' + 1 = Module.finrank ℝ E) {K : M → ℝ}
    (hdα : ∀ s, mextDeriv α.val (ι s) = σ.val (ι s))
    (hZα : ∀ s v, σ.val (ι s) ![Z (ι s), v] = α.val (ι s) ![v])
    (hK : ∀ s, (mfderiv J I ι s).range = (mvfderiv I K (ι s)).ker)
    (hKZ : ∀ s, mvfderiv I K (ι s) (Z (ι s)) ≠ 0) (s : S) :
    mfderiv J I ι s ((SmoothForm.mpullback ι hι α).reebVectorField s) =
      -(mvfderiv I K (ι s) (Z (ι s)))⁻¹ • σ.hamiltonianVectorField K (ι s) := by
  refine hσ.mfderiv_reebVectorField_mpullback_of_interior_eq hι
    (hσ.isContactForm_mpullback_of_interior_eq hι hιs hdim hdα (z := fun s ↦ Z (ι s))
      (fun s' hZ ↦ hKZ s' ?_) hZα) (hdα s) (hZα s) (hK s)
  rwa [hK s', LinearMap.mem_ker] at hZ

end SmoothTwoForm

end TauCeti
