/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Liouville.ContactType
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Geometry.Symplectic.Manifold.Flat

/-!
# Liouville domains

A **Liouville domain** is a compact exact symplectic manifold with boundary whose Liouville vector
field points outwards along the boundary. Here it is a compact domain `W` with smooth boundary
in the interior of an ambient manifold `M`, carrying a nondegenerate two-form `ω` and a primitive
`α`, `dα = ω` (`TauCeti.IsLiouvilleDomain`):

* the smooth vector field `Z` with `ι_Z ω = α`, the **Liouville field** of `α`, exists;
* `W = {f ≤ c}` for a continuous function `f`, smooth at the points of the level `f⁻¹(c)`, with
  `df(Z) > 0` along that level.

The last condition says that `Z` points strictly outwards along `f⁻¹(c)`, and makes `c` a regular
value of `f`. So `f⁻¹(c)` is a smooth hypersurface, and it is the boundary of `W`: on a manifold
without boundary, the frontier of `W` is exactly the level
(`TauCeti.frontier_setOf_le_eq_of_mvfderiv_pos`). The primitive is part of the data, as for
hypersurfaces of contact type, and the ambient form `ω` is then symplectic
(`TauCeti.IsLiouvilleDomain.isSymplectic`). Since `ω` is smooth and closed, the Liouville field
of `α` is a Liouville vector field of `ω`, `L_Z ω = ω`
(`TauCeti.isLiouvilleVectorField_mextDeriv_of_interior_eq`).

The boundary of a Liouville domain, with the atlas of a regular level, is a hypersurface of
restricted contact type with primitive `α`
(`TauCeti.IsLiouvilleDomain.exists_isRestrictedContactType`). The basic example is the unit
codisc bundle of a compact Riemannian manifold, with the canonical symplectic form and the
primitive `-λ` of the cotangent bundle
(`TauCeti.CotangentBundle.isLiouvilleDomain_codiscBundle`).

## Main definitions

* `TauCeti.IsLiouvilleDomain`: a compact domain whose boundary is crossed outwards by the
  Liouville field of an explicit primitive of a nondegenerate form.

## Main results

* `TauCeti.IsLiouvilleDomain.isSymplectic`: the ambient form is symplectic.
* `TauCeti.IsLiouvilleDomain.exists_sublevel_of_interior_eq`: every vector field `Z` with
  `ι_Z ω = α` points strictly out of a Liouville domain along its boundary.
* `TauCeti.IsLiouvilleDomain.exists_isRestrictedContactType`: the boundary is a regular level of
  a defining function, and is of restricted contact type.

## References

* K. Cieliebak, Y. Eliashberg, *From Stein to Weinstein and Back*, AMS Colloquium Publications 59,
  2012, Section 11.1 (Liouville domains).
* P. Seidel, *A biased view of symplectic cohomology*, Current Developments in Mathematics 2006,
  Section 3 (Liouville domains and their completions).
* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §1.2.
-/

public section

open Bundle Module Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M]
  [IsManifold I (⊤ : ℕ∞) M] {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} {W : Set M}
  {Z : (x : M) → TangentSpace I x}

/-- A subset `W` of a manifold `M` is a **Liouville domain** for the smooth two-form `ω`, with
primitive `α`, when `ω` is nondegenerate, `dα = ω`, `W` is compact and lies in the interior of
`M`, and the Liouville field of `α` points strictly outwards along the boundary of `W`: some smooth
vector field `Z` with `ι_Z ω = α` and some continuous function `f` and value `c` satisfy
`W = {f ≤ c}`, with `f` smooth and `df(Z) > 0` at every point of the level `f⁻¹(c)`. The
nondegeneracy of `ω` makes `Z` unique, and the condition along `f⁻¹(c)` makes `c` a regular value
of `f`, so that `W` is a compact domain with smooth boundary `f⁻¹(c)`. -/
structure IsLiouvilleDomain (ω : SmoothTwoForm I M) (α : SmoothForm I M ℝ 1) (W : Set M) :
    Prop where
  /-- The two-form of a Liouville domain is nondegenerate. -/
  isNondegenerate : ω.IsNondegenerate
  /-- The one-form of a Liouville domain is a primitive of its two-form. -/
  mextDeriv_eq : mextDeriv α.1 = ω.1
  /-- A Liouville domain is compact. -/
  isCompact : IsCompact W
  /-- A Liouville domain lies in the interior of the ambient manifold. -/
  subset_interior : W ⊆ I.interior M
  /-- The Liouville field of the primitive points strictly outwards along the boundary, the level
  `f⁻¹(c)` of a continuous function `f` with `W = {f ≤ c}` that is smooth along the level. -/
  exists_liouville_outward : ∃ Z : (x : M) → TangentSpace I x,
    ContMDiff I I.tangent (⊤ : ℕ∞) (T% Z) ∧ RoughForm.interior Z ω.1 = α.1 ∧
      ∃ (f : M → ℝ) (c : ℝ), Continuous f ∧ W = {x | f x ≤ c} ∧
        ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) (⊤ : ℕ∞) f x ∧ 0 < mvfderiv I f x (Z x)

namespace IsLiouvilleDomain

/-- **The ambient form of a Liouville domain is symplectic**: it is nondegenerate by definition,
and closed because it is exact. -/
theorem isSymplectic (h : IsLiouvilleDomain ω α W) : ω.IsSymplectic where
  isClosed := by rw [SmoothForm.isClosed_def, ← h.mextDeriv_eq, SmoothForm.mextDeriv_mextDeriv]
  isNondegenerate := h.isNondegenerate

/-- A Liouville domain is closed, as a sublevel set of a continuous function. -/
theorem isClosed (h : IsLiouvilleDomain ω α W) : IsClosed W := by
  obtain ⟨-, -, -, f, c, hf, rfl, -⟩ := h.exists_liouville_outward
  exact isClosed_le hf continuous_const

/-- **The Liouville field of a Liouville domain is smooth**: the vector field `Z` with
`ι_Z ω = α`, unique since `ω` is nondegenerate, is a smooth section of the tangent bundle. -/
theorem contMDiff_of_interior_eq (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) :
    ContMDiff I I.tangent (⊤ : ℕ∞) (T% Z) := by
  obtain ⟨Z', hZ's, hZ', -⟩ := h.exists_liouville_outward
  rwa [h.isNondegenerate.interior_injective (hZ.trans hZ'.symm)]

/-- **The Liouville field points out of a Liouville domain.** If `ι_Z ω = α`, then `W = {f ≤ c}`
for a continuous function `f`, smooth along the level `f⁻¹(c)`, with `df(Z) > 0` there. -/
theorem exists_sublevel_of_interior_eq (h : IsLiouvilleDomain ω α W)
    (hZ : RoughForm.interior Z ω.1 = α.1) :
    ∃ (f : M → ℝ) (c : ℝ), Continuous f ∧ W = {x | f x ≤ c} ∧
      ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) (⊤ : ℕ∞) f x ∧ 0 < mvfderiv I f x (Z x) := by
  obtain ⟨Z', -, hZ', hout⟩ := h.exists_liouville_outward
  rwa [h.isNondegenerate.interior_injective (hZ.trans hZ'.symm)]

/-- **The boundary of a Liouville domain is of restricted contact type.** On a finite-dimensional
manifold without boundary, a Liouville domain `W` is the sublevel set `{f ≤ c}` of a function `f`,
`C¹` along the level `f⁻¹(c)`, of which `c` is a regular value; the frontier of `W` is exactly the
level; and the level, with its atlas `TauCeti.regularLevelChartedSpace`, is a hypersurface
of restricted contact type for the primitive `α`. -/
theorem exists_isRestrictedContactType [I.Boundaryless] [FiniteDimensional ℝ E]
    (h : IsLiouvilleDomain ω α W) :
    ∃ (f : M → ℝ) (c : ℝ) (hf : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) 1 f x)
      (hreg : IsRegularValue I 𝓘(ℝ) f c), W = {x | f x ≤ c} ∧ frontier W = {x | f x = c} ∧
        letI := regularLevelChartedSpace (n := finrank ℝ E - 1) hf hreg (by rw [finrank_self])
        IsRestrictedContactType 𝓘(ℝ, Fin (finrank ℝ E - 1) → ℝ) ω.1 α.1
          (Subtype.val : {x : M // f x = c} → M) := by
  obtain ⟨Z, hZ, hZα, f, c, hfc, rfl, hf⟩ := h.exists_liouville_outward
  have hf1 : ∀ x, f x = c → ContMDiffAt I 𝓘(ℝ) 1 f x := fun x hx ↦ (hf x hx).1.of_le (by simp)
  -- The positive number `df(Z)` is a nonzero value of the differential of `f`.
  have hreg : IsRegularValue I 𝓘(ℝ) f c := isRegularValue_iff.2 fun x hx ↦
    isRegularPoint_iff_mvfderiv_ne_zero.2 fun h0 ↦ (hf x hx).2.ne' (by simp [h0])
  refine ⟨f, c, hf1, hreg, rfl, frontier_setOf_le_eq_of_mvfderiv_pos hfc
    (fun x hx ↦ (hf x hx).2), ?_⟩
  let := regularLevelChartedSpace (n := finrank ℝ E - 1) hf1 hreg (by rw [finrank_self])
  -- `mvfderiv` is `mfderiv` read in `ℝ`, so `df(Z) > 0` is transversality to the level.
  exact isRestrictedContactType_iff.2 ⟨h.mextDeriv_eq, Z, hZ, hZα,
    (isTransverseAlong_coe_scalarRegularLevel_iff hf1 hreg).2 fun x hx ↦ by
      rw [← mvfderiv_apply_eq_mfderiv_apply]
      exact (hf x hx).2.ne'⟩

end IsLiouvilleDomain

end TauCeti
