/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Contact.Basic
public import TauCeti.Geometry.Manifold.DifferentialForm.Naturality
public import TauCeti.Geometry.Manifold.VectorField.Transverse
public import TauCeti.Geometry.Symplectic.Liouville.VectorField
public import TauCeti.Geometry.Symplectic.Manifold.TwoForm

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

A hypersurface of contact type inherits a contact form: if `ι` is an immersion of codimension one
and `ω` is nondegenerate, then `ι^* α` is a contact form on `S`
(`TauCeti.IsContactType.isContactForm_mpullback`). At a point `s`, the pulled back form is
`v ↦ ω(Z, dι v)` and its exterior derivative is `ι^* ω`, so this is the linear statement that a
covector `ω(z, ·)` is contact on a hyperplane `W` not containing `z`
(`LinearMap.BilinForm.IsAlt.isContact_comp_compl₁₂`); its pointwise form is
`TauCeti.isContactFormAt_mpullback_of_interior_eq`. Neither closedness of `ω` nor compactness of
`S` is needed.

## Main definitions

* `TauCeti.IsContactType`: contact type, with an explicit primitive near the hypersurface.
* `TauCeti.IsRestrictedContactType`: restricted contact type, with an explicit global primitive.

## Main results

* `TauCeti.IsRestrictedContactType.isContactType`: restricted contact type implies contact type.
* `TauCeti.exists_isRestrictedContactType_iff`: the characterization by transverse Liouville vector
  fields.
* `TauCeti.isContactFormAt_mpullback_of_interior_eq`: the pointwise contact condition for the form
  induced on a hypersurface transverse to a Liouville field.
* `TauCeti.IsContactType.isContactForm_mpullback`: a hypersurface of contact type carries the
  contact form `ι^* α`.

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

variable [FiniteDimensional ℝ E] {Z : (x : M) → TangentSpace I x} {s : S}

/-- **The contact form of a hypersurface transverse to a Liouville field, pointwise.** Let `ω` be
nondegenerate at `ι s`, let `α` be a `C¹` primitive of `ω` there, and let `Z` satisfy
`ι_Z ω = α` at `ι s`. If `ι` is an immersion at `s` onto a hyperplane not containing `Z (ι s)`,
then `ι^* α` is a contact form at `s`. -/
theorem isContactFormAt_mpullback_of_interior_eq [IsManifold I 2 M] [IsManifold J 2 S]
    (hω : ∀ v : TangentSpace I (ι s), (∀ w, ω (ι s) ![v, w] = 0) → v = 0)
    (hdα : mextDeriv α (ι s) = ω (ι s)) (hZ : ω.interior Z (ι s) = α (ι s))
    (hι : ContMDiffAt J I 2 ι s)
    (hα : ContMDiffAt I (I.prod 𝓘(ℝ, E [⋀^Fin 1]→L[ℝ] ℝ)) 1
      (fun y ↦ TotalSpace.mk' (E [⋀^Fin 1]→L[ℝ] ℝ) y (α y)) (ι s))
    (hinj : Function.Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E)
    (hZι : Z (ι s) ∉ (mfderiv J I ι s).range) :
    IsContactFormAt (mpullback J I ι α) s := by
  set B : LinearMap.BilinForm ℝ (TangentSpace I (ι s)) :=
    MultilinearMap.toBilinMap (ω (ι s)).toMultilinearMap
  have hBapply (v w : TangentSpace I (ι s)) : B v w = ω (ι s) ![v, w] :=
    MultilinearMap.toBilinMap_apply _ v w
  have hB : B.IsAlt := MultilinearMap.isAlt_toBilinMap fun v ↦
    (ω (ι s)).map_eq_zero_of_eq _ (by simp) Fin.zero_ne_one
  have hB' : B.SeparatingLeft := fun v hv ↦ hω v fun w ↦ by rw [← hBapply]; exact hv w
  have hc := Module.Dual.isContact_iff_of_isRefl
    (fun v w h ↦ hB.isRefl _ _ h : (B.compl₁₂ (mfderiv J I ι s : TangentSpace J s →ₗ[ℝ] _)
      (mfderiv J I ι s : TangentSpace J s →ₗ[ℝ] _)).IsRefl) |>.1
    (hB.isContact_comp_compl₁₂ hB' (f := (mfderiv J I ι s : TangentSpace J s →ₗ[ℝ] _)) hinj
      hdim hZι)
  simp only [LinearMap.comp_apply, LinearMap.compl₁₂_apply, ContinuousLinearMap.coe_coe,
    hBapply] at hc
  -- The pulled back form is `v ↦ ω(Z, dι v)`, and its exterior derivative is `ι^* ω`.
  have hpull (v : TangentSpace J s) :
      mpullback J I ι α s ![v] = ω (ι s) ![Z (ι s), mfderiv J I ι s v] := by
    rw [mpullback_apply, ← hZ, RoughForm.interior_apply]
    congr 1
    ext i
    fin_cases i <;> rfl
  have hdpull (v w : TangentSpace J s) :
      mextDeriv (mpullback J I ι α) s ![v, w] =
        ω (ι s) ![mfderiv J I ι s v, mfderiv J I ι s w] := by
    rw [← mpullback_mextDeriv_at hι hα, mpullback_apply, hdα]
    congr 1
    ext i
    fin_cases i <;> rfl
  refine ⟨fun h0 ↦ hc.1 (LinearMap.ext fun v ↦ ?_), fun v hv hvw ↦ ?_⟩
  · simp [hBapply, ← hpull, h0]
  · rw [RoughForm.mem_ker, hpull] at hv
    refine hc.2 v hv fun w hw ↦ ?_
    rw [← hdpull]
    exact hvw w (by rw [RoughForm.mem_ker, hpull]; exact hw)

/-- **Hypersurfaces of contact type carry contact forms.** If `ι : S → M` is a smooth immersion
of codimension one which is of contact type for a nondegenerate two-form `ω` with primitive `α`,
then `ι^* α` is a contact form on `S`. In particular a hypersurface transverse to a Liouville
vector field `Z` of a symplectic form `ω` carries the contact form `ι^* (ι_Z ω)`. -/
theorem IsContactType.isContactForm_mpullback [IsManifold I (⊤ : ℕ∞) M] [IsManifold J (⊤ : ℕ∞) S]
    {ω : SmoothTwoForm I M} {α : SmoothForm I M ℝ 1} (hω : ω.IsNondegenerate)
    (h : IsContactType J ω.1 α.1 ι) (hι : ContMDiff J I (⊤ : ℕ∞) ι)
    (hinj : ∀ s, Function.Injective (mfderiv J I ι s)) (hdim : finrank ℝ E' + 1 = finrank ℝ E) :
    (SmoothForm.mpullback ι hι α).IsContactForm := by
  obtain ⟨U, -, hιU, hdα, Z, -, hZα, hZι⟩ := h
  rw [SmoothForm.isContactForm_iff_forall_isContactFormAt]
  intro s
  rw [SmoothForm.coe_mpullback]
  exact isContactFormAt_mpullback_of_interior_eq
    (fun v hv ↦ SmoothTwoForm.isNondegenerate_iff_separatingLeft.1 hω _ v fun w ↦ by
      simpa [SmoothBundleForm.eval₂_apply] using hv w)
    (hdα _ (hιU ⟨s, rfl⟩)) (hZα _ (hιU ⟨s, rfl⟩)) (hι.contMDiffAt.of_le (by simp))
    ((α.contMDiff (ι s)).of_le (by simp)) (hinj s) hdim (isTransverseAlong_iff.1 hZι s)

end ContactForm

end TauCeti
