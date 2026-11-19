/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.Normed.Lp.ProdLp.HemisphereGraph
public import TauCeti.Analysis.Normed.Lp.ProdLp.Sphere
public import TauCeti.Topology.Surgery.Basic

/-!
# Surgery on the standard sphere

Let `E` and `F` be real normed spaces, say `E = ℝᵏ⁺¹` and `F = ℝ^q`. The unit sphere `Sⁿ` of the
`L²` product `WithLp 2 (E × F)`, with `n = k + q`, contains the standard `k`-sphere `Sⁿ ∩ E`. Its
closed neighbourhood `‖x.snd‖ ≤ ‖x.fst‖` is a copy of `Sᵏ × D^q` through
`TauCeti.sphereProdSndLeHomeomorph`, whose inverse `(x, y) ↦ (x, y) / √(1 + ‖y‖ ^ 2)` is the
*standard framed sphere* `TauCeti.standardFramedSphere`. Its exterior is the complementary piece
`‖x.fst‖ ≤ ‖x.snd‖` (`TauCeti.sphereExterior_standardFramedSphere`), which is a copy of
`D^(k+1) × S^(q-1)` through `TauCeti.sphereProdFstLeHomeomorph`, and on the common frontier the
two identifications agree with the boundary inclusions of `Sᵏ × S^(q-1)`.

So surgery along the standard framed sphere glues two copies of `D^(k+1) × S^(q-1)` along their
common boundary by the identity, and the result is `S^(k+1) × S^(q-1)`
(`TauCeti.standardSphereSurgery`). Here `S^(k+1)` is the unit sphere of `WithLp 2 (E × ℝ)`, the
union of its closed upper and lower hemispheres, the graphs of `u ↦ ±√(1 - ‖u‖ ^ 2)` over the
closed unit ball of `E` (`TauCeti.prodHemisphereGraph`). The exterior is the upper hemisphere
times `S^(q-1)` and the glued-in `D^(k+1) × S^(q-1)` is the lower hemisphere times `S^(q-1)`.

For `k = 0` this is the classical fact that surgery on a pair of antipodal points of `Sⁿ` gives
`S¹ × S^(n-1)`, and for `E = F = ℂ` it writes `S² × S¹` as a surgery on the unknot in `S³`. When
`E` is the zero space, the standard sphere is empty and its surgery adds a disjoint copy of
`S^(q-1) = D⁰ × S^(q-1)`, the result being `S⁰ × S^(q-1)`.

## Main definitions

* `TauCeti.standardFramedSphere`: the standard framed `k`-sphere in the unit sphere of
  `WithLp 2 (E × F)`.
* `TauCeti.standardSphereSurgery`: `S^(k+1) × S^(q-1)` as the surgery along the standard framed
  sphere.

## Main results

* `TauCeti.sphereExterior_standardFramedSphere`: the exterior of the standard framed sphere is the
  piece `‖x.fst‖ ≤ ‖x.snd‖` of the unit sphere.

## References

* J. Milnor, *A procedure for killing homotopy groups of differentiable manifolds*, Proc.
  Sympos. Pure Math. 3 (1961), 39–55, Section 1 (spherical modifications, and the example of
  `Sⁿ` modified to `S^(k+1) × S^(n-k-1)`).
-/

public section

noncomputable section

open Set Topology Metric

namespace TauCeti

variable {E F : Type*} [NormedAddCommGroup E] [NormedAddCommGroup F]

/-! ### The two hemispheres of `S^(k+1)` -/

/-- The product of the hemisphere of sign `c` of `S^(k+1)` with `S^(q-1)`, as a map from
`D^(k+1) × S^(q-1)`. -/
private def capProd {c : ℝ} (hc : c ^ 2 = 1) (p : closedBall (0 : E) 1 × sphere (0 : F) 1) :
    sphere (0 : WithLp 2 (E × ℝ)) 1 × sphere (0 : F) 1 :=
  (prodHemisphereGraph hc p.1, p.2)

private theorem isClosedEmbedding_capProd {c : ℝ} (hc : c ^ 2 = 1) :
    IsClosedEmbedding (capProd (E := E) (F := F) hc) :=
  (isClosedEmbedding_prodHemisphereGraph hc).prodMap .id

/-- On the boundary `‖u‖ = 1` of `D^(k+1)` the two hemispheres agree. -/
private theorem capProd_ballSphereBoundaryInclusion {c c' : ℝ} (hc : c ^ 2 = 1)
    (hc' : c' ^ 2 = 1) (q : sphere (0 : E) 1 × sphere (0 : F) 1) :
    capProd hc (ballSphereBoundaryInclusion q) = capProd hc' (ballSphereBoundaryInclusion q) :=
  Prod.ext (prodHemisphereGraph_eq_of_norm_eq_one hc hc' (by
    rw [coe_ballSphereBoundaryInclusion_fst]
    exact norm_eq_of_mem_sphere q.1)) rfl

/-- The upper and the lower hemisphere meet only over the boundary of `D^(k+1)`. -/
private theorem mem_range_ballSphereBoundaryInclusion_of_capProd_eq
    {p p' : closedBall (0 : E) 1 × sphere (0 : F) 1}
    (h : capProd (c := 1) (one_pow 2) p = capProd (c := -1) (by norm_num) p') :
    p' ∈ range ballSphereBoundaryInclusion := by
  rw [range_ballSphereBoundaryInclusion, mem_ofPred_eq]
  exact norm_eq_one_of_prodHemisphereGraph_eq (by norm_num) (congrArg Prod.fst h)

/-- Every point of `S^(k+1) × S^(q-1)` lies on the upper or on the lower hemisphere. -/
private theorem exists_capProd_eq (y : sphere (0 : WithLp 2 (E × ℝ)) 1 × sphere (0 : F) 1) :
    (∃ p, capProd (c := 1) (one_pow 2) p = y) ∨ ∃ p, capProd (c := -1) (by norm_num) p = y := by
  rcases le_total 0 (y.1 : WithLp 2 (E × ℝ)).snd with hs | hs
  · obtain ⟨u, hu⟩ := exists_prodHemisphereGraph_eq (one_pow 2) y.1 (by simpa using hs)
    exact Or.inl ⟨(u, y.2), Prod.ext hu rfl⟩
  · obtain ⟨u, hu⟩ := exists_prodHemisphereGraph_eq (c := -1) (by norm_num) y.1 (by simpa using hs)
    exact Or.inr ⟨(u, y.2), Prod.ext hu rfl⟩

/-! ### The standard framed sphere -/

variable [NormedSpace ℝ E] [NormedSpace ℝ F]

/-- The **standard framed `k`-sphere** in the unit sphere of `WithLp 2 (E × F)`: the unit sphere
of `E`, framed by `(x, y) ↦ (x, y) / √(1 + ‖y‖ ^ 2)` on `Sᵏ × D^q`. This is the inverse of
`TauCeti.sphereProdSndLeHomeomorph`, which identifies the closed neighbourhood
`‖x.snd‖ ≤ ‖x.fst‖` of `Sᵏ` with `Sᵏ × D^q`. -/
def standardFramedSphere (p : sphere (0 : E) 1 × closedBall (0 : F) 1) :
    sphere (0 : WithLp 2 (E × F)) 1 :=
  (sphereProdSndLeHomeomorph E F).symm p

/-- The standard framed sphere is `(x, y) ↦ (x, y) / √(1 + ‖y‖ ^ 2)`. -/
@[simp]
theorem coe_standardFramedSphere_apply (p : sphere (0 : E) 1 × closedBall (0 : F) 1) :
    (standardFramedSphere p : WithLp 2 (E × F)) =
      WithLp.toLp 2 ((√(1 + ‖(p.2 : F)‖ ^ 2))⁻¹ • (p.1 : E),
        (√(1 + ‖(p.2 : F)‖ ^ 2))⁻¹ • (p.2 : F)) :=
  coe_sphereProdSndLeHomeomorph_symm_apply p

/-- The standard framed sphere is an embedding of `Sᵏ × D^q`. -/
theorem isEmbedding_standardFramedSphere :
    IsEmbedding (standardFramedSphere (E := E) (F := F)) :=
  IsEmbedding.subtypeVal.comp (sphereProdSndLeHomeomorph E F).symm.isEmbedding

/-- The image of the open tube `Sᵏ × int D^q` under the standard framed sphere is the set where
`‖x.snd‖ < ‖x.fst‖`. -/
private theorem image_standardFramedSphere_setOf_norm_lt_one :
    standardFramedSphere '' {p : sphere (0 : E) 1 × closedBall (0 : F) 1 | ‖(p.2 : F)‖ < 1} =
      {x : sphere (0 : WithLp 2 (E × F)) 1 |
        ‖(x : WithLp 2 (E × F)).snd‖ < ‖(x : WithLp 2 (E × F)).fst‖} := by
  refine Set.ext fun x ↦ ⟨?_, ?_⟩
  · rintro ⟨p, hp, rfl⟩
    have hc : 0 < (√(1 + ‖(p.2 : F)‖ ^ 2))⁻¹ := inv_pos.2 (Real.sqrt_pos.2 (by positivity))
    simp only [mem_ofPred_eq, coe_standardFramedSphere_apply, WithLp.toLp_fst, WithLp.toLp_snd,
      norm_smul, Real.norm_of_nonneg hc.le, norm_eq_of_mem_sphere p.1, mul_one]
    exact mul_lt_of_lt_one_right hc hp
  · intro (hx : ‖(x : WithLp 2 (E × F)).snd‖ < ‖(x : WithLp 2 (E × F)).fst‖)
    let y : {x : sphere (0 : WithLp 2 (E × F)) 1 | ‖(x : WithLp 2 (E × F)).snd‖ ≤
        ‖(x : WithLp 2 (E × F)).fst‖} := ⟨x, hx.le⟩
    refine ⟨sphereProdSndLeHomeomorph E F y, ?_, by simp [standardFramedSphere, y]⟩
    exact (mem_closedBall_zero_iff.1 (sphereProdSndLeHomeomorph E F y).2.2).lt_of_ne
      fun h ↦ hx.ne' ((norm_sphereProdSndLeHomeomorph_snd_eq_one_iff y).1 h)

/-- **The exterior of the standard framed sphere** is the piece `‖x.fst‖ ≤ ‖x.snd‖` of the unit
sphere, a copy of `D^(k+1) × S^(q-1)` through `TauCeti.sphereProdFstLeHomeomorph`. -/
theorem sphereExterior_standardFramedSphere :
    sphereExterior (standardFramedSphere (E := E) (F := F)) =
      {x : sphere (0 : WithLp 2 (E × F)) 1 |
        ‖(x : WithLp 2 (E × F)).fst‖ ≤ ‖(x : WithLp 2 (E × F)).snd‖} := by
  refine Set.ext fun x ↦ ?_
  rw [mem_sphereExterior, image_standardFramedSphere_setOf_norm_lt_one, mem_ofPred_eq,
    mem_ofPred_eq, not_lt]

/-- The exterior of the standard framed sphere, identified with `D^(k+1) × S^(q-1)`. -/
private def standardSphereExteriorHomeomorph :
    sphereExterior (standardFramedSphere (E := E) (F := F)) ≃ₜ
      closedBall (0 : E) 1 × sphere (0 : F) 1 :=
  (Homeomorph.setCongr sphereExterior_standardFramedSphere).trans (sphereProdFstLeHomeomorph E F)

private theorem standardSphereExteriorHomeomorph_apply
    (x : sphereExterior (standardFramedSphere (E := E) (F := F))) :
    standardSphereExteriorHomeomorph x =
      sphereProdFstLeHomeomorph E F
        ⟨x, sphereExterior_standardFramedSphere (E := E) (F := F) ▸ x.2⟩ :=
  (rfl)

/-- On the boundary `Sᵏ × S^(q-1)`, the identification of the exterior of the standard framed
sphere with `D^(k+1) × S^(q-1)` is the boundary inclusion. -/
private theorem standardSphereExteriorHomeomorph_sphereExteriorBoundaryInclusion
    (q : sphere (0 : E) 1 × sphere (0 : F) 1) :
    standardSphereExteriorHomeomorph
        (sphereExteriorBoundaryInclusion isEmbedding_standardFramedSphere.injective q) =
      ballSphereBoundaryInclusion q := by
  -- The boundary point is `(x, y) / √2`, and dividing by the norm `1 / √2` of its second
  -- component recovers `(x, y)`.
  have h2 : 0 < √(1 + 1 : ℝ) := Real.sqrt_pos.2 (by norm_num)
  have hy : ‖(q.2 : F)‖ = 1 := norm_eq_of_mem_sphere q.2
  ext
  · simp [standardSphereExteriorHomeomorph_apply, hy, norm_smul, smul_smul, abs_of_pos h2]
  · simp [standardSphereExteriorHomeomorph_apply, hy, norm_smul, smul_smul, abs_of_pos h2]

/-! ### The surgery -/

/-- **Surgery on the standard sphere.** Surgery along the standard framed `k`-sphere of `Sⁿ`, the
unit sphere of `WithLp 2 (E × F)`, gives `S^(k+1) × S^(q-1)`, the product of the unit spheres of
`WithLp 2 (E × ℝ)` and of `F`. The exterior `‖x.fst‖ ≤ ‖x.snd‖` goes to the upper hemisphere times
`S^(q-1)` and the glued-in `D^(k+1) × S^(q-1)` to the lower hemisphere times `S^(q-1)`. -/
def standardSphereSurgery :
    SphereSurgery (isEmbedding_standardFramedSphere (E := E) (F := F)).injective
      (sphere (0 : WithLp 2 (E × ℝ)) 1 × sphere (0 : F) 1) where
  exteriorEmbedding := capProd (c := 1) (one_pow 2) ∘ standardSphereExteriorHomeomorph
  isClosedEmbedding_exteriorEmbedding :=
    (isClosedEmbedding_capProd _).comp standardSphereExteriorHomeomorph.isClosedEmbedding
  ballSphereEmbedding := capProd (c := -1) (by norm_num)
  isClosedEmbedding_ballSphereEmbedding := isClosedEmbedding_capProd _
  exteriorEmbedding_sphereExteriorBoundaryInclusion q := by
    rw [Function.comp_apply,
      standardSphereExteriorHomeomorph_sphereExteriorBoundaryInclusion]
    exact capProd_ballSphereBoundaryInclusion _ _ q
  range_union_range := by
    rw [range_comp, standardSphereExteriorHomeomorph.range_coe, image_univ]
    exact eq_univ_of_forall fun y ↦ (exists_capProd_eq y).imp id id
  range_inter_range_subset := by
    rintro _ ⟨⟨x, rfl⟩, ⟨p, hp⟩⟩
    obtain ⟨q, rfl⟩ := mem_range_ballSphereBoundaryInclusion_of_capProd_eq hp.symm
    exact ⟨q, hp⟩

/-- The exterior of the standard framed sphere goes to the upper hemisphere of `S^(k+1)`: its
point `x` goes to `(u, √(1 - ‖u‖ ^ 2))` with `u = x.fst / ‖x.snd‖`. -/
@[simp]
theorem coe_standardSphereSurgery_exteriorEmbedding_apply_fst
    (x : sphereExterior (standardFramedSphere (E := E) (F := F))) :
    ((standardSphereSurgery.exteriorEmbedding x).1 : WithLp 2 (E × ℝ)) =
      WithLp.toLp 2 (‖(x : WithLp 2 (E × F)).snd‖⁻¹ • (x : WithLp 2 (E × F)).fst,
        √(1 - ‖‖(x : WithLp 2 (E × F)).snd‖⁻¹ • (x : WithLp 2 (E × F)).fst‖ ^ 2)) := by
  simp [standardSphereSurgery, capProd, prodHemisphereGraphPoint_def,
    standardSphereExteriorHomeomorph_apply]

/-- The `S^(q-1)` coordinate of the image of a point `x` of the exterior of the standard framed
sphere is `x.snd / ‖x.snd‖`. -/
@[simp]
theorem coe_standardSphereSurgery_exteriorEmbedding_apply_snd
    (x : sphereExterior (standardFramedSphere (E := E) (F := F))) :
    ((standardSphereSurgery.exteriorEmbedding x).2 : F) =
      ‖(x : WithLp 2 (E × F)).snd‖⁻¹ • (x : WithLp 2 (E × F)).snd := by
  simp [standardSphereSurgery, capProd, standardSphereExteriorHomeomorph_apply]

/-- The glued-in `D^(k+1) × S^(q-1)` goes to the lower hemisphere of `S^(k+1)`: the point `(u, v)`
goes to `(u, -√(1 - ‖u‖ ^ 2))`. -/
@[simp]
theorem coe_standardSphereSurgery_ballSphereEmbedding_apply_fst
    (p : closedBall (0 : E) 1 × sphere (0 : F) 1) :
    ((standardSphereSurgery.ballSphereEmbedding p).1 : WithLp 2 (E × ℝ)) =
      WithLp.toLp 2 ((p.1 : E), -√(1 - ‖(p.1 : E)‖ ^ 2)) := by
  simp [standardSphereSurgery, capProd, prodHemisphereGraphPoint_def]

/-- The glued-in `D^(k+1) × S^(q-1)` keeps its `S^(q-1)` coordinate. -/
@[simp]
theorem standardSphereSurgery_ballSphereEmbedding_apply_snd
    (p : closedBall (0 : E) 1 × sphere (0 : F) 1) :
    (standardSphereSurgery.ballSphereEmbedding p).2 = p.2 :=
  (rfl)

end TauCeti
