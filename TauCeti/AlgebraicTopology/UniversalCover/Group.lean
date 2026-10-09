/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.ContinuousMonoidHom
public import TauCeti.AlgebraicTopology.FundamentalGroup.TopologicalMonoid
public import TauCeti.AlgebraicTopology.UniversalCover.Classification.Pointed
public import TauCeti.AlgebraicTopology.UniversalCover.Covering

/-!
# The universal covering group of a topological group

Let `G` be a topological group. A point of the universal cover `UniversalCover (1 : G)` based at
the identity is a point `x : G` together with a homotopy class of paths from `1` to `x`. Two such
classes can be multiplied pointwise: if `p` runs from `1` to `x` and `q` from `1` to `y`, then
`t ↦ p t * q t` runs from `1` to `x * y`, and a pair of homotopies multiplies to a homotopy. With
the pointwise inverse `t ↦ (p t)⁻¹` and the constant path as identity, this makes
`UniversalCover (1 : G)` a group, and the group laws hold already for the paths, pointwise.

When `G` is locally path-connected and semilocally simply connected, so that `UniversalCover 1`
is a simply connected covering space of the identity path component, these operations are
continuous and `UniversalCover (1 : G)` is a **topological group**. Continuity is not visible from
the formula, since the topology is a quotient topology. It comes from the lifting criterion
instead: the map `(a, b) ↦ proj a * proj b` on the simply connected, locally path-connected space
`UniversalCover 1 × UniversalCover 1` lifts to a continuous map into the cover, and unique path
lifting identifies that lift with the pointwise product. The same argument handles the inverse.

The endpoint projection is then a continuous homomorphism `UniversalCover.projHom` which is a
covering map, and its kernel, a discrete normal subgroup of a connected group, is central. This is
the topological half of the simply connected covering group of a connected Lie group.

The kernel is the fundamental group `π₁(G, 1)`, for every topological group `G`. Its points are
the homotopy classes of loops at `1`, and on them the group law of the universal cover is
pointwise multiplication of loops, which in a topological group agrees with concatenation by
the Eckmann–Hilton argument (`FundamentalGroup.cast_map_prod_mul`).

## Main definitions

* `TauCeti.UniversalCover.instGroup`: the group structure on `UniversalCover (1 : G)` given by
  pointwise multiplication of paths.
* `TauCeti.UniversalCover.projHom`: the endpoint projection as a continuous homomorphism
  `UniversalCover (1 : G) →ₜ* G`.
* `TauCeti.UniversalCover.kerProjHomEquivFundamentalGroup`: the kernel of `projHom` is
  isomorphic to the fundamental group `π₁(G, 1)`.

## Main statements

* `TauCeti.UniversalCover.mk_mul_mk`, `TauCeti.UniversalCover.inv_mk`,
  `TauCeti.UniversalCover.one_def`: the group operations on representatives.
* `TauCeti.UniversalCover.instIsTopologicalGroup`: for a locally path-connected, semilocally simply
  connected `G`, the universal cover is a topological group.
* `TauCeti.UniversalCover.isCoveringMap_projHom`: the projection is a covering homomorphism.
* `TauCeti.UniversalCover.ker_projHom_le_center`: its kernel is central.
* `TauCeti.UniversalCover.discreteTopology_ker_projHom`: its kernel is discrete.
* `IsCoveringMap.continuousMulEquivUniversalCover`: a simply connected covering group is
  continuously isomorphic to the universal covering group over the base.

## References

* J. M. Lee, *Introduction to Smooth Manifolds*, 2nd ed., Springer GTM 218 (2013), Chapter 7,
  "Covering groups".
* B. C. Hall, *Lie Groups, Lie Algebras, and Representations*, 2nd ed., Springer GTM 222 (2015),
  Chapter 5.
-/

public section
noncomputable section

open scoped unitInterval

namespace TauCeti.UniversalCover

variable {G : Type*} [Group G] [TopologicalSpace G]

/-! ### The group structure -/

/-- The identity of the universal cover based at `1` is the class of the constant path. -/
instance instOne : One (UniversalCover (1 : G)) where
  one := ⟨1, Path.Homotopic.Quotient.refl 1⟩

/-- The identity is the class of the constant path. -/
theorem one_def : (1 : UniversalCover (1 : G)) = mk 1 (Path.Homotopic.Quotient.refl 1) :=
  (rfl)

@[simp]
theorem proj_one : (1 : UniversalCover (1 : G)).proj = 1 :=
  (rfl)

/-- The identity is the class of the constant based path. -/
theorem one_eq_ofBasedPath_refl :
    (1 : UniversalCover (1 : G)) = ofBasedPath 1 (BasedPath.refl 1) := by
  rw [← BasedPath.ofPath_refl, ofBasedPath_ofPath, Path.Homotopic.Quotient.mk_refl, one_def]

/-- Every point of the universal cover is the class of a path. -/
private theorem induction_on {motive : UniversalCover (1 : G) → Prop} (a : UniversalCover (1 : G))
    (h : ∀ (x : G) (p : Path 1 x), motive (mk x (.mk p))) : motive a := by
  obtain ⟨x, q⟩ := a
  induction q using Quotient.inductionOn with
  | h p => exact h x p

/-- The classes of two paths that agree pointwise are equal. -/
private theorem mk_eq_mk {x y : G} {p : Path 1 x} {q : Path 1 y} (h : ∀ t, p t = q t) :
    mk x (.mk p) = mk y (.mk q) :=
  UniversalCover.ext (by simpa using h 1) (Path.Homotopic.hpath_hext h)

variable [IsTopologicalGroup G]

/-- Multiplication on the universal cover based at `1`: the endpoints multiply, and the homotopy
classes of paths multiply pointwise (`TauCeti.UniversalCover.mk_mul_mk`). -/
instance instMul : Mul (UniversalCover (1 : G)) where
  mul a b := ⟨a.proj * b.proj,
    ((Path.Homotopic.prod a.path b.path).map ⟨fun p : G × G ↦ p.1 * p.2, continuous_mul⟩).cast
      (mul_one 1).symm rfl⟩

/-- Inversion on the universal cover based at `1`: the endpoint is inverted, and the homotopy
class of paths is inverted pointwise (`TauCeti.UniversalCover.inv_mk`). -/
instance instInv : Inv (UniversalCover (1 : G)) where
  inv a := ⟨a.proj⁻¹, (a.path.map ⟨fun x : G ↦ x⁻¹, continuous_inv⟩).cast inv_one.symm rfl⟩

/-- The product of the classes of two paths is the class of their pointwise product. -/
theorem mk_mul_mk {x y : G} (p : Path 1 x) (q : Path 1 y) :
    mk x (.mk p) * mk y (.mk q) = mk (x * y) (.mk ((p.mul q).cast (mul_one 1).symm rfl)) :=
  (rfl)

/-- The inverse of the class of a path is the class of its pointwise inverse. -/
theorem inv_mk {x : G} (p : Path 1 x) :
    (mk x (.mk p))⁻¹ = mk x⁻¹ (.mk (p.inv.cast inv_one.symm rfl)) :=
  (rfl)

@[simp]
theorem proj_mul (a b : UniversalCover (1 : G)) : (a * b).proj = a.proj * b.proj :=
  (rfl)

@[simp]
theorem proj_inv (a : UniversalCover (1 : G)) : a⁻¹.proj = a.proj⁻¹ :=
  (rfl)

/-- The product of the classes of two based paths is the class of their pointwise product. -/
theorem ofBasedPath_mul_ofBasedPath (α β : BasedPath (1 : G)) :
    ofBasedPath 1 α * ofBasedPath 1 β =
      ofBasedPath 1 (.ofPath ((α.toPath.mul β.toPath).cast (mul_one 1).symm rfl)) := by
  rw [ofBasedPath_def, ofBasedPath_def, mk_mul_mk, ofBasedPath_ofPath]

/-- The inverse of the class of a based path is the class of its pointwise inverse. -/
theorem inv_ofBasedPath (α : BasedPath (1 : G)) :
    (ofBasedPath 1 α)⁻¹ = ofBasedPath 1 (.ofPath (α.toPath.inv.cast inv_one.symm rfl)) := by
  rw [ofBasedPath_def, inv_mk, ofBasedPath_ofPath]

/-- The universal cover based at the identity of a topological group is a group under pointwise
multiplication of paths. -/
instance instGroup : Group (UniversalCover (1 : G)) where
  mul_assoc a b c := by
    induction a using induction_on
    induction b using induction_on
    induction c using induction_on
    simp only [mk_mul_mk]
    exact mk_eq_mk fun t ↦ by simp [mul_assoc]
  one_mul a := by
    induction a using induction_on
    rw [one_def, ← Path.Homotopic.Quotient.mk_refl, mk_mul_mk]
    exact mk_eq_mk fun t ↦ by simp
  mul_one a := by
    induction a using induction_on
    rw [one_def, ← Path.Homotopic.Quotient.mk_refl, mk_mul_mk]
    exact mk_eq_mk fun t ↦ by simp
  inv_mul_cancel a := by
    induction a using induction_on
    rw [inv_mk, mk_mul_mk, one_def, ← Path.Homotopic.Quotient.mk_refl]
    exact mk_eq_mk fun t ↦ by simp

/-- The endpoint projection of the universal cover based at the identity, as a continuous
homomorphism. -/
def projHom : UniversalCover (1 : G) →ₜ* G where
  toFun := proj
  map_one' := proj_one
  map_mul' := proj_mul
  continuous_toFun := continuous_proj 1

@[simp]
theorem coe_projHom : ⇑(projHom : UniversalCover (1 : G) →ₜ* G) = proj :=
  (rfl)

/-! ### The kernel of the covering homomorphism -/

/-- A point of the universal cover lies in the kernel of the covering homomorphism exactly when
it lies over the identity. -/
theorem mem_ker_projHom {a : UniversalCover (1 : G)} :
    a ∈ (projHom (G := G) : UniversalCover (1 : G) →* G).ker ↔ a.proj = 1 :=
  MonoidHom.mem_ker

/-- **The kernel of the covering homomorphism is the fundamental group.** A point of the universal
cover based at `1` lying over `1` is a homotopy class of loops at `1`, and the group law of the
universal cover, pointwise multiplication of paths, multiplies loop classes as the fundamental
group does (`FundamentalGroup.cast_map_prod_mul`). -/
def kerProjHomEquivFundamentalGroup :
    (projHom (G := G) : UniversalCover (1 : G) →* G).ker ≃* FundamentalGroup G 1 :=
  MulEquiv.symm
    { toFun a := ⟨mk 1 a.toPath, mem_ker_projHom.2 rfl⟩
      invFun z := z.1.path.cast rfl (mem_ker_projHom.1 z.2).symm
      left_inv a := Path.Homotopic.Quotient.cast_rfl_rfl a
      right_inv z := Subtype.ext <| UniversalCover.ext (mem_ker_projHom.1 z.2).symm
        (Path.Homotopic.Quotient.cast_heq _ _)
      map_mul' a b := Subtype.ext <| UniversalCover.ext (mul_one 1).symm <| by
        rw [← FundamentalGroup.cast_map_prod_mul]
        exact (Path.Homotopic.Quotient.cast_heq _ _).trans
          (Path.Homotopic.Quotient.cast_heq _ _).symm }

/-- A loop class at the identity corresponds to the point of the universal cover over `1` that it
defines. -/
@[simp]
theorem coe_kerProjHomEquivFundamentalGroup_symm_apply (a : FundamentalGroup G 1) :
    (kerProjHomEquivFundamentalGroup.symm a : UniversalCover (1 : G)) = mk 1 a.toPath :=
  (rfl)

/-- A point of the universal cover over `1` corresponds to its homotopy class of loops. -/
theorem kerProjHomEquivFundamentalGroup_apply
    (z : (projHom (G := G) : UniversalCover (1 : G) →* G).ker) :
    (kerProjHomEquivFundamentalGroup z).toPath = z.1.path.cast rfl (mem_ker_projHom.1 z.2).symm :=
  (rfl)

/-! ### The topological group structure -/

variable [LocallyPathConnectedSpace G] [SemilocallySimplyConnectedSpace G]

/-- A continuous map into the universal cover that starts at the identity and lies over the
pointwise product of two based paths agrees, at time `1`, with the product of their classes. -/
private theorem apply_one_eq_mul_of_lifts {g : I → UniversalCover (1 : G)} (hg : Continuous g)
    (α β : BasedPath (1 : G)) (hproj : ∀ t, (g t).proj = α t * β t) (h₀ : g 0 = 1) :
    g 1 = ofBasedPath 1 α * ofBasedPath 1 β := by
  rw [ofBasedPath_mul_ofBasedPath]
  exact apply_one_eq_ofBasedPath hg _ (fun t ↦ by simp [hproj])
    (by rw [h₀, one_eq_ofBasedPath_refl])

/-- Multiplication on the universal cover is continuous: it is the lift through the covering
projection of `(a, b) ↦ proj a * proj b` that sends `(1, 1)` to `1`. -/
private theorem continuous_mul_universalCover :
    Continuous fun p : UniversalCover (1 : G) × UniversalCover (1 : G) ↦ p.1 * p.2 := by
  let f : C(UniversalCover (1 : G) × UniversalCover (1 : G), G) :=
    ⟨fun p ↦ p.1.proj * p.2.proj, by fun_prop⟩
  obtain ⟨F, ⟨hF₀, hF⟩, -⟩ := (isCoveringMap (1 : G)).existsUnique_continuousMap_lifts f (1, 1) 1
    (by simp [f])
  have hFproj (p) : (F p).proj = p.1.proj * p.2.proj := congrFun hF p
  refine F.continuous.congr fun p ↦ ?_
  obtain ⟨α, hα⟩ := surjective_ofBasedPath 1 p.1
  obtain ⟨β, hβ⟩ := surjective_ofBasedPath 1 p.2
  have h := apply_one_eq_mul_of_lifts
    (g := fun t ↦ F (ofBasedPath 1 (α.initialSegmentFamily t),
      ofBasedPath 1 (β.initialSegmentFamily t))) (by fun_prop) α β
    (fun t ↦ by simp [hFproj]) (by simpa [← one_eq_ofBasedPath_refl] using hF₀)
  simpa [hα, hβ] using h

/-- Inversion on the universal cover is continuous: it is the lift through the covering projection
of `a ↦ (proj a)⁻¹` that fixes `1`. -/
private theorem continuous_inv_universalCover :
    Continuous fun a : UniversalCover (1 : G) ↦ a⁻¹ := by
  let f : C(UniversalCover (1 : G), G) := ⟨fun a ↦ a.proj⁻¹, by fun_prop⟩
  obtain ⟨F, ⟨hF₀, hF⟩, -⟩ := (isCoveringMap (1 : G)).existsUnique_continuousMap_lifts f 1 1
    (by simp [f])
  have hFproj (a) : (F a).proj = a.proj⁻¹ := congrFun hF a
  refine F.continuous.congr fun a ↦ ?_
  obtain ⟨α, rfl⟩ := surjective_ofBasedPath 1 a
  have h := apply_one_eq_ofBasedPath (g := fun t ↦ F (ofBasedPath 1 (α.initialSegmentFamily t)))
    (by fun_prop) (.ofPath (α.toPath.inv.cast inv_one.symm rfl)) (fun t ↦ by simp [hFproj])
    (by simpa [← one_eq_ofBasedPath_refl] using hF₀)
  simpa [inv_ofBasedPath] using h

/-- The universal cover based at the identity of a locally path-connected, semilocally simply
connected topological group is a topological group. -/
instance instIsTopologicalGroup : IsTopologicalGroup (UniversalCover (1 : G)) where
  continuous_mul := continuous_mul_universalCover
  continuous_inv := continuous_inv_universalCover

/-- The endpoint projection is a covering homomorphism. -/
theorem isCoveringMap_projHom : IsCoveringMap (projHom : UniversalCover (1 : G) →ₜ* G) :=
  isCoveringMap 1

/-- A point of the universal cover lying over the identity is central: conjugating it by a
variable element gives a continuous map into the discrete fibre over `1` from a connected space. -/
theorem mem_center_of_proj_eq_one {z : UniversalCover (1 : G)} (hz : z.proj = 1) :
    z ∈ Subgroup.center (UniversalCover (1 : G)) := by
  refine Subgroup.mem_center_iff.mpr fun g ↦ ?_
  have h := (isCoveringMap (1 : G)).const_of_comp (g := fun g ↦ g * z * g⁻¹) (by fun_prop)
    (fun a a' ↦ by simp [hz]) g 1
  rw [← mul_inv_eq_iff_eq_mul, h]
  simp

/-- The kernel of the covering homomorphism is central. -/
theorem ker_projHom_le_center :
    (projHom (G := G) : UniversalCover (1 : G) →* G).ker ≤
      Subgroup.center (UniversalCover (1 : G)) :=
  fun _ hz ↦ mem_center_of_proj_eq_one (mem_ker_projHom.1 hz)

/-- The kernel of the covering homomorphism is discrete: it is the fibre of the covering map over
the identity. -/
instance discreteTopology_ker_projHom :
    DiscreteTopology (projHom (G := G) : UniversalCover (1 : G) →* G).ker :=
  (Homeomorph.setCongr (t := proj ⁻¹' {(1 : G)})
    (Set.ext fun _ ↦ by simp)).symm.discreteTopology

end TauCeti.UniversalCover

namespace IsCoveringMap

open TauCeti

variable {E G : Type*} [Group E] [TopologicalSpace E]
  [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
  [SimplyConnectedSpace E] [LocallyPathConnectedSpace E]
  [LocallyPathConnectedSpace G] [SemilocallySimplyConnectedSpace G]
  {p : E →ₜ* G}

/-- A pointed homeomorphism from a simply connected covering group to the universal cover,
commuting with the two projections. -/
private theorem exists_universalCoverHomeomorph (hp : IsCoveringMap p) :
    ∃ h : E ≃ₜ UniversalCover (1 : G), h 1 = 1 ∧ UniversalCover.projHom ∘ h = p :=
  hp.exists_homeomorph_comp_eq_of_simplyConnectedSpace
    (q := UniversalCover.projHom) (x := 1) (e₀ := 1) (f₀ := 1)
      UniversalCover.isCoveringMap_projHom p.map_one (by simp)

/-- The pointed homeomorphism from a simply connected covering group to the universal cover. -/
private noncomputable def universalCoverHomeomorph (hp : IsCoveringMap p) :
    E ≃ₜ UniversalCover (1 : G) :=
  hp.exists_universalCoverHomeomorph.choose

private theorem universalCoverHomeomorph_one (hp : IsCoveringMap p) :
    hp.universalCoverHomeomorph 1 = 1 :=
  hp.exists_universalCoverHomeomorph.choose_spec.1

private theorem universalCoverHomeomorph_proj (hp : IsCoveringMap p) :
    UniversalCover.projHom ∘ hp.universalCoverHomeomorph = p :=
  hp.exists_universalCoverHomeomorph.choose_spec.2

variable [IsTopologicalGroup E]

/-- A simply connected, locally path-connected covering group is continuously isomorphic to the
universal covering group of its base. The isomorphism sends the identity to the identity and
commutes with the covering projections.

The underlying pointed homeomorphism is supplied by uniqueness of the universal cover. Its
multiplicativity follows by comparing two lifts on `E × E`: multiplication before and after the
homeomorphism gives continuous lifts of the same map and both send `(1, 1)` to `1`. -/
noncomputable def continuousMulEquivUniversalCover (hp : IsCoveringMap p) :
    E ≃ₜ* UniversalCover (1 : G) :=
  ContinuousMulEquiv.mk' hp.universalCoverHomeomorph fun a b ↦ by
    let f : E × E → UniversalCover (1 : G) :=
      fun z ↦ hp.universalCoverHomeomorph (z.1 * z.2)
    let g : E × E → UniversalCover (1 : G) :=
      fun z ↦ hp.universalCoverHomeomorph z.1 * hp.universalCoverHomeomorph z.2
    have hfg : f = g := UniversalCover.isCoveringMap_projHom.eq_of_comp_eq
      (g₁ := f) (g₂ := g) (by fun_prop) (by fun_prop) (by
        funext z
        -- The lift-uniqueness goal is phrased using `projHom`; expose its endpoint function so
        -- the projection law for the chosen homeomorphism and `proj_mul` can be applied.
        change (hp.universalCoverHomeomorph (z.1 * z.2)).proj =
          (hp.universalCoverHomeomorph z.1 * hp.universalCoverHomeomorph z.2).proj
        rw [UniversalCover.proj_mul]
        have hproj (e : E) : (hp.universalCoverHomeomorph e).proj = p e :=
          congrFun hp.universalCoverHomeomorph_proj e
        rw [hproj, hproj, hproj, map_mul])
      (1, 1) (by simp [f, g, hp.universalCoverHomeomorph_one])
    exact congrFun hfg (a, b)

/-- The universal-cover projection after the canonical comparison is the original covering
homomorphism. -/
@[simp]
theorem projHom_comp_continuousMulEquivUniversalCover (hp : IsCoveringMap p) :
    UniversalCover.projHom.comp
      (hp.continuousMulEquivUniversalCover : E →ₜ* UniversalCover (1 : G)) = p := by
  ext e
  exact congrFun hp.universalCoverHomeomorph_proj e

/-- Applying the universal-cover projection to the canonical comparison agrees with the original
covering homomorphism. -/
@[simp]
theorem continuousMulEquivUniversalCover_apply_proj (hp : IsCoveringMap p) (e : E) :
    UniversalCover.projHom (hp.continuousMulEquivUniversalCover e) = p e :=
  DFunLike.congr_fun hp.projHom_comp_continuousMulEquivUniversalCover e

/-- Projecting the inverse image under the canonical comparison agrees with the universal-cover
projection. -/
@[simp]
theorem continuousMulEquivUniversalCover_symm_apply_proj (hp : IsCoveringMap p)
    (x : UniversalCover (1 : G)) :
    p (hp.continuousMulEquivUniversalCover.symm x) = UniversalCover.projHom x := by
  -- `ContinuousMulEquiv.mk'` reuses the private homeomorphism definitionally; expose that
  -- underlying map so its inverse and projection equations apply.
  change p (hp.universalCoverHomeomorph.symm x) = UniversalCover.projHom x
  symm
  calc
    UniversalCover.projHom x = UniversalCover.projHom
        (hp.universalCoverHomeomorph (hp.universalCoverHomeomorph.symm x)) := by simp
    _ = p (hp.universalCoverHomeomorph.symm x) :=
      congrFun hp.universalCoverHomeomorph_proj _

/-- The canonical comparison is the unique continuous homomorphism to the universal covering
group that commutes with the covering projections. -/
theorem continuousMulEquivUniversalCover_unique (hp : IsCoveringMap p)
    (f : E →ₜ* UniversalCover (1 : G)) (hf : UniversalCover.projHom.comp f = p) :
    f = (hp.continuousMulEquivUniversalCover : E →ₜ* UniversalCover (1 : G)) := by
  apply DFunLike.ext _ _
  intro e
  have hcomp : (fun e ↦ UniversalCover.projHom (f e)) =
      fun e ↦ UniversalCover.projHom (hp.continuousMulEquivUniversalCover e) := by
    funext x
    exact (DFunLike.congr_fun hf x).trans
      (DFunLike.congr_fun hp.projHom_comp_continuousMulEquivUniversalCover x).symm
  exact congrFun (UniversalCover.isCoveringMap_projHom.eq_of_comp_eq
    f.continuous hp.continuousMulEquivUniversalCover.continuous
    hcomp 1 (by simp)) e

end IsCoveringMap
