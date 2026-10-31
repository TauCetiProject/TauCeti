/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.VectorField.Transverse
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm
import TauCeti.Geometry.Manifold.DifferentialForm.Naturality

/-!
# Hypersurfaces of contact type

Let `ω` be a two-form on a manifold `M` and let `ι : S → M` be a map, typically the inclusion of
an embedded hypersurface. The hypersurface is of **contact type** when some Liouville vector field
(`L_Z ω = ω`) defined near it is transverse to it, and of **restricted contact type** when such a
field exists on all of `M`. These are the hypersurfaces whose characteristic foliations are
preserved, up to conjugation, by the flow of `Z`, which is how existence of closed characteristics
on them is deduced from almost existence.

For a closed `ω`, a Liouville vector field `Z` is the same as a primitive `α = ι_Z ω` of `ω`
(`TauCeti.isLiouvilleVectorField_iff_mextDeriv_interior_eq`), and when `ω` is nondegenerate the
primitive determines the field. The definitions below keep the primitive explicit:

* `TauCeti.IsContactType J ω α ι`: on some open neighbourhood `U` of the image of `ι`, `dα = ω`, and
  some vector field `Z`, smooth on `U` and satisfying `ι_Z ω = α` on `U`, is transverse along `ι`;
* `TauCeti.IsRestrictedContactType J ω α ι`: `dα = ω` on `M`, and some smooth vector field `Z` on
  `M` with `ι_Z ω = α` is transverse along `ι`.

The primitive is part of the data because a Liouville vector field need not be the Liouville field
of a given primitive: on the plane, `x ∂_x + ∂_y` is a Liouville vector field of `d(x dy)` whose
primitive is `x dy - dx`, not `x dy` (`Prod.curryLeft_extDeriv_realPlaneXDy_ne`).

A hypersurface of restricted contact type is of contact type, with the same primitive
(`TauCeti.IsRestrictedContactType.isContactType`). For a closed `C¹` form `ω`, a hypersurface is of
restricted contact type for some primitive exactly when some smooth Liouville vector field of `ω`
is transverse along it (`TauCeti.exists_isRestrictedContactType_iff`), which is the definition of
McDuff and Salamon. The basic example is the unit cosphere bundle of a Riemannian manifold, with
the primitive `-λ` of the canonical symplectic form of the cotangent bundle
(`TauCeti.CotangentBundle.isRestrictedContactType_cosphereBundle`).

A hypersurface of contact type is a contact manifold: if `ω` is nondegenerate and `ι` is an
immersion of codimension one of contact type for `ω` with primitive `α`, then `ι^* α` is a contact
form (`TauCeti.IsContactType.isContactForm_mpullback`). At a point `ι s` the image `W` of the
differential of `ι` is a hyperplane and `Z` lies outside it. The covector `α = ι_Z ω` cannot
vanish on `W`, since it vanishes on `Z` and `ω` is nondegenerate. A vector of `W ∩ ker α` that is
`ω`-orthogonal to `W ∩ ker α` is also `ω`-orthogonal to `Z`, hence to all of `ker α`, so it is a
multiple of `Z` lying in `W` and therefore zero. The pointwise version
(`TauCeti.isContactFormAt_mpullback`) only uses the data at a single point.

## Main definitions

* `TauCeti.IsContactType`: contact type, with an explicit primitive near the hypersurface.
* `TauCeti.IsRestrictedContactType`: restricted contact type, with an explicit global primitive.

## Main results

* `TauCeti.IsRestrictedContactType.isContactType`: restricted contact type implies contact type.
* `TauCeti.exists_isRestrictedContactType_iff`: the characterization by transverse Liouville vector
  fields.
* `TauCeti.isContactFormAt_mpullback`, `TauCeti.IsContactType.isContactForm_mpullback`: the
  primitive restricts to a contact form on a hypersurface of contact type.

## References

* D. McDuff, D. Salamon, *Introduction to Symplectic Topology*, 3rd ed., Oxford, 2017,
  Section 3.5 (hypersurfaces of contact type).
* H. Hofer, E. Zehnder, *Symplectic Invariants and Hamiltonian Dynamics*, Birkhäuser, 1994,
  Chapter 4.
-/

public section

open Bundle Module Set
open scoped Manifold

namespace TauCeti

variable {E H M : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} [TopologicalSpace M] [ChartedSpace H M] [IsManifold I 1 M]
  {E' H' S : Type*} [NormedAddCommGroup E'] [NormedSpace ℝ E'] [TopologicalSpace H']
  {J : ModelWithCorners ℝ E' H'} [TopologicalSpace S] [ChartedSpace H' S]
  {ω : RoughForm I M ℝ 2} {α : RoughForm I M ℝ 1} {ι : S → M}

variable (J) in
/-- A map `ι : S → M`, typically an embedded hypersurface, is **of contact type** for the two-form
`ω`, with primitive `α`, when on some open neighbourhood `U` of the image of `ι` the one-form `α` is
a primitive of `ω`, `dα = ω`, and some vector field `Z`, smooth on `U` and satisfying `ι_Z ω = α`
on `U`, is transverse along `ι`. When `ω` is smooth, such a `Z` is a Liouville vector field of
`ω` on `U`. -/
def IsContactType (ω : RoughForm I M ℝ 2) (α : RoughForm I M ℝ 1) (ι : S → M) : Prop :=
  ∃ U : Set M, IsOpen U ∧ range ι ⊆ U ∧ (∀ x ∈ U, mextDeriv α x = ω x) ∧
    ∃ Z : (x : M) → TangentSpace I x, ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Z) U ∧
      (∀ x ∈ U, ω.interior Z x = α x) ∧ IsTransverseAlong J Z ι

variable (J) in
/-- A map `ι : S → M`, typically an embedded hypersurface, is **of restricted contact type** for
the two-form `ω`, with primitive `α`, when `α` is a primitive of `ω` on all of `M`, `dα = ω`, and
some smooth vector field `Z` on `M` with `ι_Z ω = α` is transverse along `ι`. For a closed
`C¹` form `ω`, such a `Z` is a Liouville vector field of `ω`
(`TauCeti.exists_isRestrictedContactType_iff`). -/
def IsRestrictedContactType (ω : RoughForm I M ℝ 2) (α : RoughForm I M ℝ 1) (ι : S → M) : Prop :=
  mextDeriv α = ω ∧ ∃ Z : (x : M) → TangentSpace I x, ContMDiff I I.tangent (⊤ : ℕ∞) (T% Z) ∧
    ω.interior Z = α ∧ IsTransverseAlong J Z ι

/-- The defining characterization of contact type. -/
theorem isContactType_iff :
    IsContactType J ω α ι ↔ ∃ U : Set M, IsOpen U ∧ range ι ⊆ U ∧
      (∀ x ∈ U, mextDeriv α x = ω x) ∧ ∃ Z : (x : M) → TangentSpace I x,
        ContMDiffOn I I.tangent (⊤ : ℕ∞) (T% Z) U ∧ (∀ x ∈ U, ω.interior Z x = α x) ∧
          IsTransverseAlong J Z ι :=
  Iff.rfl

/-- The defining characterization of restricted contact type. -/
theorem isRestrictedContactType_iff :
    IsRestrictedContactType J ω α ι ↔ mextDeriv α = ω ∧ ∃ Z : (x : M) → TangentSpace I x,
      ContMDiff I I.tangent (⊤ : ℕ∞) (T% Z) ∧ ω.interior Z = α ∧ IsTransverseAlong J Z ι :=
  Iff.rfl

namespace IsRestrictedContactType

/-- The primitive of a hypersurface of restricted contact type is a primitive: `dα = ω`. -/
theorem mextDeriv_eq (h : IsRestrictedContactType J ω α ι) : mextDeriv α = ω :=
  h.1

/-- **Restricted contact type implies contact type**, with the same primitive: take the whole
manifold as the neighbourhood of the hypersurface. -/
theorem isContactType (h : IsRestrictedContactType J ω α ι) : IsContactType J ω α ι := by
  obtain ⟨hα, Z, hZ, hZα, hZι⟩ := h
  exact ⟨univ, isOpen_univ, subset_univ _, fun x _ ↦ congrFun hα x, Z, hZ.contMDiffOn,
    fun x _ ↦ congrFun hZα x, hZι⟩

end IsRestrictedContactType

/-- **Restricted contact type through Liouville vector fields.** For a closed `C¹` two-form `ω`,
a map `ι` is of restricted contact type for some primitive of `ω` exactly when some smooth
Liouville vector field `Z` of `ω` on `M` is transverse along `ι`; the primitive is then
`ι_Z ω`. -/
theorem exists_isRestrictedContactType_iff (hω : IsSmoothForm I 1 ω) (hdω : mextDeriv ω = 0) :
    (∃ α, IsRestrictedContactType J ω α ι) ↔
      ∃ Z : (x : M) → TangentSpace I x, ContMDiff I I.tangent (⊤ : ℕ∞) (T% Z) ∧
        IsLiouvilleVectorField ω Z ∧ IsTransverseAlong J Z ι := by
  have hω' := hω.contMDiff.mdifferentiable one_ne_zero
  constructor
  · rintro ⟨α, hdα, Z, hZ, hZα, hZι⟩
    refine ⟨Z, hZ, ?_, hZι⟩
    rw [isLiouvilleVectorField_iff_mextDeriv_interior_eq hω' (hZ.mdifferentiable (by simp)) hdω,
      hZα, hdα]
  · rintro ⟨Z, hZ, hZω, hZι⟩
    exact ⟨ω.interior Z,
      (isLiouvilleVectorField_iff_mextDeriv_interior_eq hω' (hZ.mdifferentiable (by simp))
        hdω).1 hZω, Z, hZ, rfl, hZι⟩

/-! ### The contact form of a hypersurface of contact type -/

section ContactForm

variable [FiniteDimensional ℝ E]

/-- **The primitive restricts to a contact form on a transverse hypersurface**, pointwise. Let
`ι : S → M` be `C²` at `s`, with injective differential there, from a manifold of one dimension
less. Let `ω` be nondegenerate at `ι s`, let `α` be a `C¹` primitive of `ω` at `ι s`, and let `z`
be a tangent vector at `ι s`, outside the image of the differential of `ι`, with `ι_z ω = α`.
Then the pullback `ι^* α` is a contact form at `s`. -/
theorem isContactFormAt_mpullback [IsManifold I 2 M] [IsManifold J 2 S] {s : S}
    (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hι : ContMDiffAt J I 2 ι s) (hιs : Function.Injective (mfderiv J I ι s))
    (hω : ∀ v : TangentSpace I (ι s), (∀ w, ω (ι s) ![v, w] = 0) → v = 0)
    (hα : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) 1
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) (ι s))
    (hdα : mextDeriv α (ι s) = ω (ι s)) {z : TangentSpace I (ι s)}
    (hz : z ∉ (mfderiv J I ι s).range) (hzα : ∀ v, ω (ι s) ![z, v] = α (ι s) ![v]) :
    IsContactFormAt (mpullback J I ι α) s := by
  obtain ⟨B, hBω⟩ : ∃ B : LinearMap.BilinForm ℝ (TangentSpace I (ι s)),
      ∀ v w, B v w = ω (ι s) ![v, w] :=
    ⟨(ω (ι s)).toMultilinearMap.toBilinMap, fun _ _ ↦ MultilinearMap.toBilinMap_apply _ _ _⟩
  have hB : B.IsAlt := fun v ↦ by
    rw [hBω]
    exact (ω (ι s)).map_eq_zero_of_eq ![v, v] (i := 0) (j := 1) rfl Fin.zero_ne_one
  let L : TangentSpace J s →ₗ[ℝ] TangentSpace I (ι s) := mfderiv J I ι s
  have : FiniteDimensional ℝ (TangentSpace J s) := Module.Finite.of_injective L hιs
  have hLz : LinearMap.range L ⊔ ℝ ∙ z = ⊤ := by
    refine Submodule.eq_top_of_finrank_eq ?_
    rw [Submodule.finrank_sup_span_singleton hz, LinearMap.finrank_range_of_inj hιs]
    exact hdim
  obtain ⟨hne, hnd⟩ := (Module.Dual.isContact_iff_of_isRefl (B := B.compl₁₂ L L)
    fun x y hxy ↦ hB.isRefl (L x) (L y) hxy).1
    (Module.Dual.isContact_comp_compl₁₂ hB (fun v hv ↦ hω v fun w ↦ hBω v w ▸ hv w) hιs hz hLz)
  simp only [L, LinearMap.comp_apply, LinearMap.compl₁₂_apply, ContinuousLinearMap.coe_coe, hBω,
    hzα, ne_eq, LinearMap.ext_iff, LinearMap.zero_apply, not_forall] at hne hnd
  -- Evaluate the pullback and its exterior derivative through the differential of `ι`.
  have h₁ (u : TangentSpace J s) :
      mpullback J I ι α s ![u] = α (ι s) ![mfderiv J I ι s u] := by
    rw [mpullback_apply]
    congr 1
    ext i
    fin_cases i
    rfl
  have h₂ (u w : TangentSpace J s) : mextDeriv (mpullback J I ι α) s ![u, w] =
      ω (ι s) ![mfderiv J I ι s u, mfderiv J I ι s w] := by
    rw [← mpullback_mextDeriv_at hι hα, mpullback_apply, hdα]
    congr 1
    ext i
    fin_cases i <;> rfl
  obtain ⟨u₀, hu₀⟩ := hne
  refine ⟨fun h0 ↦ hu₀ ?_, fun u hu huw ↦ hnd u ?_ fun w hw ↦ ?_⟩
  · rw [← h₁, h0, ContinuousAlternatingMap.coe_zero, Pi.zero_apply]
  · rwa [RoughForm.mem_ker, h₁] at hu
  · rw [← h₂]
    exact huw w (by rwa [RoughForm.mem_ker, h₁])

/-- **Hypersurfaces of contact type carry contact forms.** If a smooth map `ι : S → M` with
injective differentials, from a manifold of one dimension less, is of contact type for a
nondegenerate two-form `σ`, with primitive `α`, then the pullback `ι^* α` is a contact form on
`S`. -/
theorem IsContactType.isContactForm_mpullback [IsManifold I (⊤ : ℕ∞) M] [IsManifold J 2 S]
    {σ : SmoothTwoForm I M} (hσ : σ.IsNondegenerate)
    {α : SmoothForm I M ℝ 1} (h : IsContactType J σ.1 α.1 ι) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hιs : ∀ s, Function.Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E) :
    (SmoothForm.mpullback ι hι α).IsContactForm := by
  obtain ⟨U, -, hιU, hdα, Z, -, hZα, hZι⟩ := h
  refine SmoothForm.isContactForm_iff_forall_isContactFormAt.2 fun s ↦ ?_
  rw [SmoothForm.coe_mpullback]
  have hs : ι s ∈ U := hιU (mem_range_self s)
  refine isContactFormAt_mpullback hdim ((hι s).of_le (by simp)) (hιs s) (fun v hv ↦ ?_)
    ((α.contMDiff (ι s)).of_le (by simp)) (hdα _ hs) (isTransverseAlong_iff.1 hZι s) fun v ↦ ?_
  · exact (SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 hσ) _ v fun w ↦ by
      simpa [SmoothBundleForm.eval₂_apply] using hv w
  · simpa only [RoughForm.interior_apply] using congrArg (fun a ↦ a ![v]) (hZα _ hs)

end ContactForm

end TauCeti
