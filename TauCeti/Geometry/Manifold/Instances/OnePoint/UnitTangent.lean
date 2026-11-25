/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Manifold.Instances.OnePoint.Sphere
public import TauCeti.Geometry.Manifold.Instances.Stiefel.UnitTangent
public import TauCeti.Geometry.Manifold.Diffeomorph.Tangent
import TauCeti.Analysis.Matrix.EuclideanLin
import TauCeti.Geometry.Manifold.Instances.OnePoint.Moebius
import TauCeti.Geometry.Manifold.MFDeriv.NormedSpace
import TauCeti.Topology.Algebra.Matrix.ProjectiveSpecialLinearGroup.RotationGroup

/-!
# The unit tangent bundle of the Riemann sphere is `SO(3)`

The round metric of the Riemann sphere `OnePoint ℂ` is `4π` times its Fubini–Study metric,
`g(a, b) = 4π ω_FS(a, i b)`, where `ω_FS` (`OnePoint.fubiniStudyForm`) is normalized to total area
one: it is the metric pulled back from the round unit sphere `S²` along the diffeomorphism
`σ = OnePoint.diffeomorphSphere v ι` (`OnePoint.inner_mfderiv_diffeomorphSphere`). Its unit
tangent bundle is the set of tangent vectors `a` with `4π ω_FS(a, i a) = 1` in the tangent bundle
`TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)` of the Riemann sphere, regarded as a real surface.

This file transports the identification of the unit tangent bundle of the round sphere `S²` with
`SO(3)` (`TauCeti.sphereUnitTangentHomeomorphSpecialOrthogonalGroup`) to the Riemann sphere. The
tangent map of `σ` is a homeomorphism of tangent bundles carrying the unit tangent vectors of the
Riemann sphere onto those of `S²` (`OnePoint.unitTangentHomeomorphSphere`). Composing, a unit
tangent vector `a` at `x` goes to the rotation whose columns are the oriented orthonormal frame
`(σ x, dσ a, σ x ⨯₃ dσ a)` of `ℝ³` (`OnePoint.unitTangentHomeomorphSpecialOrthogonalGroup`).

This identification is equivariant. If a map `g` of the Riemann sphere is a rotation `Q` of the
round sphere, in the sense that `σ ∘ g = Q ∘ σ`, its tangent map preserves the round unit tangent
bundle and rotates every frame by `Q`, so it acts on `SO(3)` by left multiplication by `Q`
(`OnePoint.unitTangentHomeomorphSpecialOrthogonalGroup_tangentMap`). For the north pole
`(0, 0, 1)` and the isometry `z ↦ (Re z, -Im z, 0)` (`OnePoint.sphereCoordsIsometry`), `σ` is the
Pauli model `OnePoint.homeomorphSphere` of the Riemann sphere
(`OnePoint.diffeomorphSphere_sphereCoordsIsometry_apply`), which intertwines the Möbius action
of `U ∈ SU(2)` with the rotation `SU2.toSO3 U`. Hence the tangent action of `U` on the round unit
tangent bundle is left multiplication by `SU2.toSO3 U` on `SO(3)`
(`OnePoint.unitTangentHomeomorphSpecialOrthogonalGroup_tangentMap_toPSL_smul`). Since the double
cover `SU(2) → SO(3)` is surjective with the same kernel `{1, -1}` as `SU(2) → PSL(2, ℂ)`, the group
`PSU(2)` of rotations of the Riemann sphere acts simply transitively on its round unit tangent
vectors (`OnePoint.existsUnique_tangentMap_smul_eq`).

## Main definitions

* `OnePoint.roundUnitTangentBundle`: the unit tangent bundle of the Riemann sphere for its round
  metric, the tangent vectors `a` with `4π ω_FS(a, i a) = 1`.
* `OnePoint.unitTangentHomeomorphSphere v ι`: the tangent map of `σ` identifies the unit tangent
  bundle of the Riemann sphere for its round metric with that of the round sphere `S²`.
* `OnePoint.unitTangentHomeomorphSpecialOrthogonalGroup v ι`: the unit tangent bundle of the
  Riemann sphere for its round metric is homeomorphic to `SO(3)`.

## Main results

* `OnePoint.norm_mfderiv_diffeomorphSphere_sq`: `‖dσ a‖² = 4π ω_FS(a, i a)`.
* `OnePoint.coe_unitTangentHomeomorphSpecialOrthogonalGroup_apply`: the rotation attached to a
  unit tangent vector.
* `OnePoint.diffeomorphSphere_proj_unitTangentHomeomorphSpecialOrthogonalGroup_symm_apply` and,
  in the same namespace,
  `mfderiv_mfderiv_diffeomorphSphere_unitTangentHomeomorphSpecialOrthogonalGroup_symm_apply`:
  the unit tangent vector `a` at `x` attached to a rotation `A` has `σ x` equal to the first
  column of `A` and `dσ a` equal to its second column.
* `OnePoint.tangentMap_mem_roundUnitTangentBundle` and
  `OnePoint.unitTangentHomeomorphSpecialOrthogonalGroup_tangentMap`: a map acting on the round
  sphere by a rotation `Q` preserves the round unit tangent bundle and acts on `SO(3)` by left
  multiplication by `Q`.
* `OnePoint.unitTangentHomeomorphSpecialOrthogonalGroup_tangentMap_toPSL_smul`: the tangent action
  of `U ∈ SU(2)` is left multiplication by `SU2.toSO3 U`.
* `OnePoint.existsUnique_tangentMap_smul_eq`: `PSU(2)` acts simply transitively on the round unit
  tangent bundle.

## References

* J. M. Lee, *Introduction to Riemannian Manifolds*, 2nd ed., Springer GTM 176 (2018), Chapter 3
  (stereographic coordinates on the round sphere).
* W. Fulton and J. Harris, *Representation Theory: A First Course*, Graduate Texts in Mathematics
  129, Springer, 1991, §7.3 (the double cover `SU(2) → SO(3)` through the Pauli matrices).
-/

public section

open Bundle Matrix Metric Module WithLp TauCeti TauCeti.Matrix.SpecialOrthogonalGroup
open scoped Manifold MatrixGroups TauCeti.ComplexManifold

noncomputable section

namespace OnePoint

/-- **The unit tangent bundle of the Riemann sphere for its round metric.** The tangent vectors `a`
of the Riemann sphere with `4π ω_FS(a, i a) = 1`, the unit vectors of its round metric
`g(a, b) = 4π ω_FS(a, i b)`. -/
def roundUnitTangentBundle : Set (TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)) :=
  {p | 4 * Real.pi *
    SmoothBundleForm.eval₂ fubiniStudyForm p.proj p.snd (Complex.I * (id p.snd : ℂ)) = 1}

/-- A tangent vector `a` of the Riemann sphere is a round unit vector when
`4π ω_FS(a, i a) = 1`. -/
@[simp]
theorem mem_roundUnitTangentBundle_iff (p : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)) :
    p ∈ roundUnitTangentBundle ↔
      4 * Real.pi *
        SmoothBundleForm.eval₂ fubiniStudyForm p.proj p.snd (Complex.I * (id p.snd : ℂ)) = 1 :=
  Iff.rfl

section Sphere

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E] [Fact (finrank ℝ E = 2 + 1)]
  (v : sphere (0 : E) 1) (ι : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (v : E))ᗮ)

/-- **The round norm on the Riemann sphere.** The round norm of the image of a tangent vector `a`
of the Riemann sphere under the differential of `σ = diffeomorphSphere v ι` is given by
`‖dσ a‖² = 4π ω_FS(a, i a)`. -/
theorem norm_mfderiv_diffeomorphSphere_sq (x : OnePoint ℂ) (a : ℂ) :
    ‖mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) x a‖ ^ 2 =
      4 * Real.pi * SmoothBundleForm.eval₂ fubiniStudyForm x a (Complex.I * a) := by
  rw [← real_inner_self_eq_norm_sq, inner_mfderiv_diffeomorphSphere]

/-- **The unit tangent bundle of the Riemann sphere is that of the round sphere.** The tangent map
of `σ = diffeomorphSphere v ι` carries the tangent vectors `a` of the Riemann sphere with
`4π ω_FS(a, i a) = 1`, the unit vectors of its round metric, onto the unit tangent vectors of the
round sphere `S²`. -/
def unitTangentHomeomorphSphere :
    roundUnitTangentBundle ≃ₜ {q : TangentBundle (𝓡 2) (sphere (0 : E) 1) | ‖q.snd‖ = 1} :=
  ((diffeomorphSphere v ι).tangentHomeomorph (by simp)).subtype fun p ↦ by
    rw [mem_roundUnitTangentBundle_iff, Set.mem_ofPred_eq, Diffeomorph.coe_tangentHomeomorph,
      tangentMap_snd, tangentMap_proj, ← pow_left_inj₀ (norm_nonneg _) zero_le_one two_ne_zero,
      one_pow]
    -- The norm here is that of the tangent space at the projection of the tangent map, which is
    -- only definitionally the one at `σ p.proj`, so close the goal by the equation itself.
    exact (congrArg (· = (1 : ℝ)) (norm_mfderiv_diffeomorphSphere_sq v ι p.proj p.snd)).symm.to_iff

/-- The unit tangent vector `a` at `x` goes to the unit tangent vector `dσ a` at `σ x`. -/
@[simp]
theorem coe_unitTangentHomeomorphSphere_apply (p : roundUnitTangentBundle) :
    (unitTangentHomeomorphSphere v ι p : TangentBundle (𝓡 2) (sphere (0 : E) 1)) =
      tangentMap 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) p :=
  by simp [unitTangentHomeomorphSphere]

/-- The inverse sends the unit tangent vector `w` at `y` to `(dσ)⁻¹ w` at `σ⁻¹ y`. -/
@[simp]
theorem coe_unitTangentHomeomorphSphere_symm_apply
    (q : {q : TangentBundle (𝓡 2) (sphere (0 : E) 1) | ‖q.snd‖ = 1}) :
    ((unitTangentHomeomorphSphere v ι).symm q : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)) =
      tangentMap (𝓡 2) 𝓘(ℝ, ℂ) (diffeomorphSphere v ι).symm q :=
  by simp [unitTangentHomeomorphSphere]

end Sphere

section SpecialOrthogonalGroup

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

variable (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  (ι : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin 3)))ᗮ)

/-- **The unit tangent bundle of the Riemann sphere is `SO(3)`.** A tangent vector `a` of the
Riemann sphere at `x` with `4π ω_FS(a, i a) = 1`, a unit vector for its round metric, goes to the
rotation whose columns are the oriented orthonormal frame `(σ x, dσ a, σ x ⨯₃ dσ a)` of `ℝ³`, where
`σ = diffeomorphSphere v ι` and `dσ a` is read in `ℝ³`. -/
def unitTangentHomeomorphSpecialOrthogonalGroup :
    roundUnitTangentBundle ≃ₜ specialOrthogonalGroup (Fin 3) ℝ :=
  (unitTangentHomeomorphSphere v ι).trans sphereUnitTangentHomeomorphSpecialOrthogonalGroup

/-- The rotation attached to the unit tangent vector `a` at `x` has columns `σ x`, `dσ a` and
`σ x ⨯₃ dσ a`, with `dσ a` read in `ℝ³` through the differential of the inclusion of the sphere. -/
@[simp]
theorem coe_unitTangentHomeomorphSpecialOrthogonalGroup_apply (p : roundUnitTangentBundle) :
    (unitTangentHomeomorphSpecialOrthogonalGroup v ι p : Matrix (Fin 3) (Fin 3) ℝ) =
      ofFrame (ofLp (diffeomorphSphere v ι p.val.proj : EuclideanSpace ℝ (Fin 3)))
        (ofLp (mvfderiv (𝓡 2)
          ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
          (diffeomorphSphere v ι p.val.proj)
          (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) p.val.proj p.val.snd))) := by
  simp only [unitTangentHomeomorphSpecialOrthogonalGroup, Homeomorph.trans_apply,
    coe_sphereUnitTangentHomeomorphSpecialOrthogonalGroup_apply]
  -- The base point and the fibre component both depend on the image of `p`, so rewrite it as a
  -- whole: it is the tangent map of `σ` at `p`.
  generalize hq : (unitTangentHomeomorphSphere v ι p).val = q
  rw [coe_unitTangentHomeomorphSphere_apply] at hq
  subst hq
  rw [tangentMap_proj, tangentMap_snd]

/-- The unit tangent vector attached to a rotation `A` lies over the point of the Riemann sphere
sent by `σ` to the first column of `A`. -/
@[simp]
theorem diffeomorphSphere_proj_unitTangentHomeomorphSpecialOrthogonalGroup_symm_apply
    (A : specialOrthogonalGroup (Fin 3) ℝ) :
    diffeomorphSphere v ι ((unitTangentHomeomorphSpecialOrthogonalGroup v ι).symm A).val.proj =
      toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ).col 0) := by
  have h := congr_arg (fun B : specialOrthogonalGroup (Fin 3) ℝ ↦
    ((B : Matrix (Fin 3) (Fin 3) ℝ).col 0))
    ((unitTangentHomeomorphSpecialOrthogonalGroup v ι).apply_symm_apply A)
  simp only [coe_unitTangentHomeomorphSpecialOrthogonalGroup_apply, ofFrame_col_zero] at h
  rw [← h, toLp_ofLp]

/-- The unit tangent vector `a` at `x` attached to a rotation `A` has `dσ a`, read in `ℝ³` through
the differential of the inclusion of the sphere, equal to the second column of `A`. -/
@[simp]
theorem mfderiv_mfderiv_diffeomorphSphere_unitTangentHomeomorphSpecialOrthogonalGroup_symm_apply
    (A : specialOrthogonalGroup (Fin 3) ℝ) :
    mfderiv (𝓡 2) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3))
        ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
        (diffeomorphSphere v ι ((unitTangentHomeomorphSpecialOrthogonalGroup v ι).symm A).val.proj)
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι)
          ((unitTangentHomeomorphSpecialOrthogonalGroup v ι).symm A).val.proj
          ((unitTangentHomeomorphSpecialOrthogonalGroup v ι).symm A).val.snd) =
      toLp 2 ((A : Matrix (Fin 3) (Fin 3) ℝ).col 1) := by
  have h := congr_arg (fun B : specialOrthogonalGroup (Fin 3) ℝ ↦
    ((B : Matrix (Fin 3) (Fin 3) ℝ).col 1))
    ((unitTangentHomeomorphSpecialOrthogonalGroup v ι).apply_symm_apply A)
  simp only [coe_unitTangentHomeomorphSpecialOrthogonalGroup_apply, ofFrame_col_one] at h
  rw [← h, toLp_ofLp, mvfderiv_apply_eq_mfderiv_apply]

end SpecialOrthogonalGroup

/-! ### Rotations act on unit frames by left multiplication -/

section Naturality

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

variable (v : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1)
  (ι : ℂ ≃ₗᵢ[ℝ] (ℝ ∙ (v : EuclideanSpace ℝ (Fin 3)))ᗮ)
  {g : OnePoint ℂ → OnePoint ℂ} {Q : Matrix (Fin 3) (Fin 3) ℝ}

/-- If `σ ∘ g = Q ∘ σ` for `σ = diffeomorphSphere v ι`, then the differential of `σ` read in `ℝ³`
carries the differential of `g` to `Q`: `dσ (dg a) = Q (dσ a)`. -/
private theorem ofLp_mvfderiv_mfderiv_diffeomorphSphere_mfderiv {x : OnePoint ℂ}
    (hg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x)
    (hσ : ∀ y, ofLp (diffeomorphSphere v ι (g y) : EuclideanSpace ℝ (Fin 3)) =
      Q *ᵥ ofLp (diffeomorphSphere v ι y : EuclideanSpace ℝ (Fin 3)))
    (a : TangentSpace 𝓘(ℝ, ℂ) x) :
    ofLp (mvfderiv (𝓡 2)
        ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
        (diffeomorphSphere v ι (g x))
        (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) (g x)
          (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x a))) =
      Q *ᵥ ofLp (mvfderiv (𝓡 2)
        ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
        (diffeomorphSphere v ι x) (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) x a)) := by
  -- Read `σ` in `ℝ³` as `F = (↑) ∘ σ`; the hypothesis says `F ∘ g = Q ∘ F`.
  set F : OnePoint ℂ → EuclideanSpace ℝ (Fin 3) :=
    ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3)) ∘
      diffeomorphSphere v ι
  have hF (y : OnePoint ℂ) : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, EuclideanSpace ℝ (Fin 3)) F y :=
    ((contMDiff_coe_sphere.comp (diffeomorphSphere v ι).contMDiff).mdifferentiableAt
      (by simp))
  have hd (y : OnePoint ℂ) (c : TangentSpace 𝓘(ℝ, ℂ) y) :
      mvfderiv (𝓡 2)
          ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
          (diffeomorphSphere v ι y) (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) y c) =
        mvfderiv 𝓘(ℝ, ℂ) F y c :=
    (mvfderiv_comp_apply y ((contMDiff_coe_sphere _).mdifferentiableAt one_ne_zero)
      ((diffeomorphSphere v ι).mdifferentiable (by simp) y) c).symm
  have hcomp : F ∘ g = Matrix.toEuclideanCLM (𝕜 := ℝ) Q ∘ F := by
    funext y
    exact WithLp.ofLp_injective 2 ((hσ y).trans (Matrix.ofLp_toEuclideanCLM Q _).symm)
  rw [hd, hd, ← Matrix.ofLp_toEuclideanCLM, ← ContinuousLinearMap.mvfderiv_comp_apply _ (hF x),
    ← hcomp, mvfderiv_comp_apply x (hF (g x)) hg]

/-- **A rotation of the round sphere preserves its unit tangent bundle.** If a differentiable map
`g` of the Riemann sphere satisfies `σ ∘ g = Q ∘ σ` for `σ = diffeomorphSphere v ι` and an
orthogonal matrix `Q`, its tangent map sends round unit tangent vectors to round unit tangent
vectors. -/
theorem tangentMap_mem_roundUnitTangentBundle (hQ : Q ∈ orthogonalGroup (Fin 3) ℝ)
    (hσ : ∀ y, ofLp (diffeomorphSphere v ι (g y) : EuclideanSpace ℝ (Fin 3)) =
      Q *ᵥ ofLp (diffeomorphSphere v ι y : EuclideanSpace ℝ (Fin 3)))
    {p : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g p.proj)
    (hp : p ∈ roundUnitTangentBundle) :
    tangentMap 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g p ∈ roundUnitTangentBundle := by
  obtain ⟨x, a⟩ := p
  rw [mem_roundUnitTangentBundle_iff, tangentMap_proj, tangentMap_snd] at ⊢
  rw [mem_roundUnitTangentBundle_iff] at hp
  -- Both conditions say that the image under `dσ` is a unit vector of the round sphere. The
  -- conditions are stated with `id` reading tangent vectors in `ℂ`, so they are matched to
  -- `norm_mfderiv_diffeomorphSphere_sq` as equations rather than rewritten.
  refine (norm_mfderiv_diffeomorphSphere_sq v ι (g x) (mfderiv 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g x a)).symm.trans
    (Eq.trans ?_ ((norm_mfderiv_diffeomorphSphere_sq v ι x a).trans hp))
  rw [norm_tangentSpace_sphere, norm_tangentSpace_sphere]
  congr 1
  -- The matrix `Q` acts on `ℝ³` as a linear isometry.
  have h := (Matrix.UnitaryGroup.toLinearIsometryEquiv (⟨Q, hQ⟩ : unitaryGroup (Fin 3) ℝ)).norm_map
    (mvfderiv (𝓡 2)
      ((↑) : sphere (0 : EuclideanSpace ℝ (Fin 3)) 1 → EuclideanSpace ℝ (Fin 3))
      (diffeomorphSphere v ι x) (mfderiv 𝓘(ℝ, ℂ) (𝓡 2) (diffeomorphSphere v ι) x a))
  rw [Matrix.UnitaryGroup.toLinearIsometryEquiv_apply] at h
  rw [← h, ← ofLp_mvfderiv_mfderiv_diffeomorphSphere_mfderiv v ι hg hσ, toLp_ofLp]

/-- **Rotations act on unit frames by left multiplication.** If a differentiable map `g` of the
Riemann sphere satisfies `σ ∘ g = Q ∘ σ` for `σ = diffeomorphSphere v ι` and a rotation `Q`, then
the identification of the round unit tangent bundle with `SO(3)` sends the image of a unit tangent
vector under the tangent map of `g` to `Q` times the rotation of the vector: the frame
`(σ x, dσ a, σ x ⨯₃ dσ a)` is rotated by `Q`. -/
theorem unitTangentHomeomorphSpecialOrthogonalGroup_tangentMap
    (Q : specialOrthogonalGroup (Fin 3) ℝ)
    (hσ : ∀ y, ofLp (diffeomorphSphere v ι (g y) : EuclideanSpace ℝ (Fin 3)) =
      (Q : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ ofLp (diffeomorphSphere v ι y : EuclideanSpace ℝ (Fin 3)))
    (p : roundUnitTangentBundle)
    (hg : MDifferentiableAt 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g (p : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)).proj) :
    unitTangentHomeomorphSpecialOrthogonalGroup v ι
        ⟨tangentMap 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) g p,
          tangentMap_mem_roundUnitTangentBundle v ι
            (mem_specialOrthogonalGroup_iff.1 Q.property).1 hσ hg p.property⟩ =
      Q * unitTangentHomeomorphSpecialOrthogonalGroup v ι p := by
  obtain ⟨⟨x, a⟩, hp⟩ := p
  ext1
  rw [coe_unitTangentHomeomorphSpecialOrthogonalGroup_apply, Submonoid.coe_mul,
    coe_unitTangentHomeomorphSpecialOrthogonalGroup_apply, ← ofFrame_mulVec_mulVec Q.property]
  simp only [tangentMap_proj, tangentMap_snd]
  rw [hσ]
  exact congrArg _ (ofLp_mvfderiv_mfderiv_diffeomorphSphere_mfderiv v ι hg hσ a)

end Naturality

/-! ### The Pauli model and the action of `SU(2)` -/

section Pauli

attribute [local instance] finrank_euclideanSpace_fin_succ_fact

/-- The Möbius transformation of an element of `SU(2)` is differentiable on the Riemann sphere,
regarded as a real surface. -/
private theorem mdifferentiable_toPSL_smul (U : specialUnitaryGroup (Fin 2) ℂ) :
    MDifferentiable 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) fun x : OnePoint ℂ ↦ specialUnitaryGroup.toPSL U • x :=
  (contMDiff_const_smul (I := 𝓘(ℝ, ℂ)) (n := 1) _).mdifferentiable one_ne_zero

/-- The Pauli model intertwines the Möbius transformation of `U ∈ SU(2)` with the rotation
`SU2.toSO3 U`. -/
private theorem ofLp_diffeomorphSphere_toPSL_smul (U : specialUnitaryGroup (Fin 2) ℂ)
    (x : OnePoint ℂ) :
    ofLp (diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry
        (specialUnitaryGroup.toPSL U • x) : EuclideanSpace ℝ (Fin 3)) =
      (SU2.toSO3 U : Matrix (Fin 3) (Fin 3) ℝ) *ᵥ
        ofLp (diffeomorphSphere (homeomorphSphere ∞) sphereCoordsIsometry x :
          EuclideanSpace ℝ (Fin 3)) := by
  simp only [diffeomorphSphere_sphereCoordsIsometry_apply, coe_homeomorphSphere, ofLp_toLp,
    specialUnitaryGroup.sphereCoords_toPSL_smul]

/-- **`PSU(2)` preserves the round unit tangent bundle.** The tangent map of the Möbius
transformation of `U ∈ SU(2)` sends round unit tangent vectors of the Riemann sphere to round unit
tangent vectors. -/
theorem tangentMap_toPSL_smul_mem_roundUnitTangentBundle (U : specialUnitaryGroup (Fin 2) ℂ)
    {p : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)} (hp : p ∈ roundUnitTangentBundle) :
    tangentMap 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (specialUnitaryGroup.toPSL U • ·) p ∈ roundUnitTangentBundle :=
  tangentMap_mem_roundUnitTangentBundle _ _
    (mem_specialOrthogonalGroup_iff.1 (SU2.toSO3 U).property).1
    (ofLp_diffeomorphSphere_toPSL_smul U) (mdifferentiable_toPSL_smul U _) hp

/-- **The unit tangent bundle of the Riemann sphere is `SO(3)`, equivariantly.** For the Pauli
model of the round sphere, the identification of the round unit tangent bundle of the Riemann
sphere with `SO(3)` intertwines the tangent action of `U ∈ SU(2)`, through its Möbius
transformation, with left multiplication by its rotation `SU2.toSO3 U` under the double cover
`SU(2) → SO(3)`. -/
theorem unitTangentHomeomorphSpecialOrthogonalGroup_tangentMap_toPSL_smul
    (U : specialUnitaryGroup (Fin 2) ℂ) (p : roundUnitTangentBundle) :
    unitTangentHomeomorphSpecialOrthogonalGroup (homeomorphSphere ∞) sphereCoordsIsometry
        ⟨tangentMap 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (specialUnitaryGroup.toPSL U • ·) p,
          tangentMap_toPSL_smul_mem_roundUnitTangentBundle U p.property⟩ =
      SU2.toSO3 U *
        unitTangentHomeomorphSpecialOrthogonalGroup (homeomorphSphere ∞) sphereCoordsIsometry p :=
  unitTangentHomeomorphSpecialOrthogonalGroup_tangentMap _ _ _
    (ofLp_diffeomorphSphere_toPSL_smul U) p (mdifferentiable_toPSL_smul U _)

/-- **`PSU(2)` acts simply transitively on the round unit tangent bundle.** For any two round unit
tangent vectors `p` and `q` of the Riemann sphere there is exactly one Möbius transformation `g` in
`PSU(2)`, the image of `SU(2)` in `PSL(2, ℂ)`, whose tangent map sends `p` to `q`. -/
theorem existsUnique_tangentMap_smul_eq (p q : roundUnitTangentBundle) :
    ∃! g ∈ (specialUnitaryGroup.toPSL : specialUnitaryGroup (Fin 2) ℂ →* PSL(2, ℂ)).range,
      tangentMap 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (g • ·) p = (q : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)) := by
  set Φ := unitTangentHomeomorphSpecialOrthogonalGroup (homeomorphSphere ∞) sphereCoordsIsometry
  -- In `SO(3)` the unique rotation taking the frame of `p` to that of `q` is `Φ q * (Φ p)⁻¹`.
  have key (U : specialUnitaryGroup (Fin 2) ℂ) :
      tangentMap 𝓘(ℝ, ℂ) 𝓘(ℝ, ℂ) (specialUnitaryGroup.toPSL U • ·) p =
          (q : TangentBundle 𝓘(ℝ, ℂ) (OnePoint ℂ)) ↔
        SU2.toSO3 U = Φ q * (Φ p)⁻¹ := by
    rw [eq_mul_inv_iff_mul_eq, ← unitTangentHomeomorphSpecialOrthogonalGroup_tangentMap_toPSL_smul,
      Φ.injective.eq_iff, Subtype.ext_iff]
  obtain ⟨U, hU⟩ := SU2.toSO3_surjective (Φ q * (Φ p)⁻¹)
  refine ⟨specialUnitaryGroup.toPSL U, ⟨⟨U, rfl⟩, (key U).2 hU⟩, ?_⟩
  rintro _ ⟨⟨V, rfl⟩, hV⟩
  -- Two elements of `SU(2)` with the same rotation differ by an element of the common kernel.
  exact SU2.toPSL_eq_toPSL_iff.2 (((key V).1 hV).trans hU.symm)

end Pauli

end OnePoint

