/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Analysis.InnerProductSpace.Orthonormal.Family
public import TauCeti.Topology.ComplexProjectiveSpace.Sphere2
public import TauCeti.Topology.Grassmannian.ForgetLast
public import TauCeti.Topology.MappingSpace.Evaluation

/-!
# The projective lines of `CPⁿ` as two-spheres

An ordered orthonormal two-frame `f = (f₀, f₁)` of `ℂⁿ⁺¹` spans a complex plane, whose projective
line in `CPⁿ` is the image of `[a : b] ↦ [a f₀ + b f₁]`
(`TauCeti.ComplexProjectiveSpace.lineMap`). Read through the homeomorphism `CP¹ ≃ₜ S²` induced
by the Hopf map `h : S³ → S²` (`TauCeti.ComplexProjectiveSpace.homeomorphSphere2`), this
parametrizes the line by the two-sphere: the map `σ_f : S² → CPⁿ`, `h (a, b) ↦ [a f₀ + b f₁]`
(`TauCeti.ComplexProjectiveSpace.lineSphereFamily`), is injective, sends the north pole to `[f₀]`
and the south pole to `[f₁]`, depends continuously on the frame, and is unchanged when both
vectors of the frame are multiplied by the same unit complex number. It is equivariant under the
unitary group. On `CP¹` itself, `σ_f` is a bijection `S² → CP¹` for every frame.

In the proof of Proposition 6.38 of Barraud–Damian–Humilière–Oancea, a point `p` of `CPⁿ` and a
unit tangent vector at `p` determine a unique complex projective line through `p` tangent to it,
a round two-sphere, and these spheres form the family `σ : T¹CPⁿ → Map(S², CPⁿ)` over `CPⁿ`. In
the frame description, `p = [f₀]`, the unit tangent vectors at `p` are the unit vectors `f₁` of the
complex orthogonal complement of `f₀`, and the line through `p` tangent to `f₁` is the projective
line of `(f₀, f₁)`. The family `σ_f` of all frames lies over `CPⁿ` through evaluation at the north
pole (`TauCeti.ComplexProjectiveSpace.mappingSpaceEval_comp_lineSphereFamily`), and since it is
invariant under the diagonal circle it factors through the unit tangent bundle. Over the point
`p = [u]`, the based family `σ_p : S(u^⊥) → Map_*(S², CPⁿ)`, `w ↦ σ_{(u, w)}`
(`TauCeti.ComplexProjectiveSpace.lineSphereFamilyFiber`), is the family of two-spheres through `p`
whose class `σ_{p*}[S(u^⊥)]` the source shows to be nonzero in `H_{2n-1}(Ω²CPⁿ)`; that
computation is not part of this file.

## Main declarations

* `TauCeti.ComplexProjectiveSpace.lineVector`: the embedding `(a, b) ↦ a f₀ + b f₁` of unit
  spheres `S³ → S²ⁿ⁺¹`, with `coe_lineVector_apply`, `lineVector_smul`, `isometry_lineVector`
  and `lineVector_injective`.
* `TauCeti.ComplexProjectiveSpace.lineMap`: `(f, [a : b]) ↦ [a f₀ + b f₁]`, jointly continuous,
  with `lineMap_mk_lineVector`, `lineMap_mk` and `lineMap_mk_single_zero`.
* `TauCeti.ComplexProjectiveSpace.lineSphereFamily`: the projective line of a frame as a map
  `S² → CPⁿ`, with `lineSphereFamily_apply_hopfSphere2`, `lineSphereFamily_apply_north`,
  `lineSphereFamily_apply_south`, `lineSphereFamily_injective`,
  `lineSphereFamily_eq_of_smul`, `lineSphereFamily_unitaryMap` and
  `lineSphereFamily_bijective`.
* `TauCeti.ComplexProjectiveSpace.lineSphereFamilyFiber`: the based family over a point, with
  `lineSphereFamilyFiber_apply_south`.

## References

* J.-F. Barraud, M. Damian, V. Humilière, A. Oancea, *Floer homology with DG coefficients.
  Applications to cotangent bundles*, arXiv:2404.07953, §6.4.5, proof of Proposition 6.38.
-/

public section

noncomputable section

open Metric Real ComplexConjugate Matrix

namespace TauCeti

namespace ComplexProjectiveSpace

/-! ### The projective line of an orthonormal two-frame -/

section Line

variable {n : ℕ}

/-- **The embedding of unit spheres of an orthonormal two-frame**: the isometric embedding
`S³ → S²ⁿ⁺¹`, `(a, b) ↦ a f₀ + b f₁`, which covers the projective line of `f`. -/
def lineVector (f : finiteOrthonormalFrame ℂ 2 (n + 1)) :
    C(sphere (0 : EuclideanSpace ℂ (Fin 2)) 1, sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1) :=
  ⟨f.property.synthesisMapIsometry.unitSphereMap, LinearIsometry.continuous_unitSphereMap _⟩

/-- The embedding of unit spheres of `f` sends `(a, b)` to `a f₀ + b f₁`. -/
@[simp]
theorem coe_lineVector_apply (f : finiteOrthonormalFrame ℂ 2 (n + 1))
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    (lineVector f v : EuclideanSpace ℂ (Fin (n + 1))) =
      (v : EuclideanSpace ℂ (Fin 2)) 0 • WithLp.toLp 2 (f.val 0) +
        (v : EuclideanSpace ℂ (Fin 2)) 1 • WithLp.toLp 2 (f.val 1) := by
  simp [lineVector, Fin.sum_univ_two]

/-- The embedding of unit spheres of `f` commutes with unit complex scalars. -/
theorem lineVector_smul (f : finiteOrthonormalFrame ℂ 2 (n + 1)) (c : sphere (0 : ℂ) 1)
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) : lineVector f (c • v) = c • lineVector f v :=
  Subtype.ext <| by simp [lineVector]

/-- The embedding of unit spheres of `f` is an isometry. -/
theorem isometry_lineVector (f : finiteOrthonormalFrame ℂ 2 (n + 1)) : Isometry (lineVector f) :=
  LinearIsometry.isometry_unitSphereMap _

/-- The embedding of unit spheres of `f` is injective. -/
theorem lineVector_injective (f : finiteOrthonormalFrame ℂ 2 (n + 1)) :
    Function.Injective (lineVector f) :=
  (isometry_lineVector f).injective

private theorem continuous_lineVector :
    Continuous fun q : finiteOrthonormalFrame ℂ 2 (n + 1) ×
        sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ↦
      lineVector q.1 q.2 := by
  refine continuous_induced_rng.2 ?_
  simp only [Function.comp_def, coe_lineVector_apply]
  have hv (i : Fin 2) : Continuous fun q : finiteOrthonormalFrame ℂ 2 (n + 1) ×
      sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ↦ (q.2 : EuclideanSpace ℂ (Fin 2)) i :=
    (PiLp.continuous_apply 2 _ i).comp (continuous_subtypeVal.comp continuous_snd)
  have hf (i : Fin 2) : Continuous fun q : finiteOrthonormalFrame ℂ 2 (n + 1) ×
      sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 ↦
        (WithLp.toLp 2 (q.1.val i) : EuclideanSpace ℂ (Fin (n + 1))) :=
    (PiLp.continuous_toLp 2 _).comp ((continuous_apply i).comp
      (continuous_subtypeVal.comp continuous_fst))
  exact ((hv 0).smul (hf 0)).add ((hv 1).smul (hf 1))

variable (n) in
/-- **The projective line of an orthonormal two-frame**: `(f, [a : b]) ↦ [a f₀ + b f₁]`, as a
jointly continuous map `V₂(ℂⁿ⁺¹) × CP¹ → CPⁿ`. -/
def lineMap :
    C(finiteOrthonormalFrame ℂ 2 (n + 1) × ComplexProjectiveSpace 1, ComplexProjectiveSpace n) where
  toFun q := ComplexProjectiveSpace.lift 1 (fun v ↦ mk n (lineVector q.1 v))
    (fun c v ↦ by rw [lineVector_smul, mk_smul]) q.2
  continuous_toFun := by
    -- `id × mk` is a quotient map, through which the map is `(f, v) ↦ [a f₀ + b f₁]`.
    rw [(IsOpenQuotientMap.id.prodMap (isOpenQuotientMap_mk 1)).isQuotientMap.continuous_iff]
    exact ((continuous_mk n).comp continuous_lineVector).congr fun q ↦
      (ComplexProjectiveSpace.lift_mk 1 (fun v ↦ mk n (lineVector q.1 v)) _ q.2).symm

/-- **The projective line of `f` is covered by its embedding of unit spheres**: it sends `[v]` to
`[lineVector f v]`. -/
theorem lineMap_mk_lineVector (f : finiteOrthonormalFrame ℂ 2 (n + 1))
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1) :
    lineMap n (f, mk 1 v) = mk n (lineVector f v) :=
  ComplexProjectiveSpace.lift_mk 1 _ _ v

/-- The projective line of `f` sends `[a : b]` to `[a f₀ + b f₁]`. -/
theorem lineMap_mk (f : finiteOrthonormalFrame ℂ 2 (n + 1))
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (hx : (x : EuclideanSpace ℂ (Fin (n + 1))) =
      (v : EuclideanSpace ℂ (Fin 2)) 0 • WithLp.toLp 2 (f.val 0) +
        (v : EuclideanSpace ℂ (Fin 2)) 1 • WithLp.toLp 2 (f.val 1)) :
    lineMap n (f, mk 1 v) = mk n x := by
  obtain rfl : x = lineVector f v := Subtype.ext (hx.trans (coe_lineVector_apply f v).symm)
  exact lineMap_mk_lineVector f v

/-- **The projective line of `f` passes through `[f₀]`**: it sends `[1 : 0]` to `[f₀]`. -/
@[simp]
theorem lineMap_mk_single_zero (f : finiteOrthonormalFrame ℂ 2 (n + 1)) :
    lineMap n (f, mk 1 ⟨EuclideanSpace.single 0 1, by simp⟩) = mk n (f.toSphere 0) :=
  lineMap_mk f _ _ (by simp)

variable (n) in
/-- **The projective line of an orthonormal two-frame as a two-sphere**: the map
`σ_f : S² → CPⁿ`, `h (a, b) ↦ [a f₀ + b f₁]`, read through `CP¹ ≃ₜ S²`, depending continuously on
the frame `f`. -/
def lineSphereFamily :
    C(finiteOrthonormalFrame ℂ 2 (n + 1), C(Sphere2, ComplexProjectiveSpace n)) :=
  ((lineMap n).comp ((ContinuousMap.id _).prodMap
    (homeomorphSphere2.symm : C(Sphere2, ComplexProjectiveSpace 1)))).curry

/-- The two-sphere of a frame is its projective line, read through `CP¹ ≃ₜ S²`. -/
theorem lineSphereFamily_apply (f : finiteOrthonormalFrame ℂ 2 (n + 1)) (x : Sphere2) :
    lineSphereFamily n f x = lineMap n (f, homeomorphSphere2.symm x) :=
  (rfl)

/-- **The two-sphere of a frame `f` sends `h (a, b)` to `[a f₀ + b f₁]`**, where `h` is the Hopf
map. Since the Hopf map is onto, this determines the two-sphere. -/
theorem lineSphereFamily_apply_hopfSphere2 (f : finiteOrthonormalFrame ℂ 2 (n + 1))
    (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (hx : (x : EuclideanSpace ℂ (Fin (n + 1))) =
      (v : EuclideanSpace ℂ (Fin 2)) 0 • WithLp.toLp 2 (f.val 0) +
        (v : EuclideanSpace ℂ (Fin 2)) 1 • WithLp.toLp 2 (f.val 1)) :
    lineSphereFamily n f (hopfSphere2 v) = mk n x := by
  rw [lineSphereFamily_apply, homeomorphSphere2_symm_hopfSphere2, lineMap_mk f v x hx]

/-- **The north pole of the two-sphere of `f` is `[f₀]`.** -/
@[simp]
theorem lineSphereFamily_apply_north (f : finiteOrthonormalFrame ℂ 2 (n + 1)) :
    lineSphereFamily n f Sphere2.north = mk n (f.toSphere 0) := by
  rw [← hopfSphere2_single_zero, lineSphereFamily_apply_hopfSphere2 f _ (f.toSphere 0) (by simp)]

/-- **The south pole of the two-sphere of `f` is `[f₁]`.** -/
@[simp]
theorem lineSphereFamily_apply_south (f : finiteOrthonormalFrame ℂ 2 (n + 1)) :
    lineSphereFamily n f Sphere2.south = mk n (f.toSphere 1) := by
  rw [← hopfSphere2_single_one, lineSphereFamily_apply_hopfSphere2 f _ (f.toSphere 1) (by simp)]

/-- **The family lies over `CPⁿ`**: evaluation at the north pole sends the two-sphere of `f` to
`[f₀]`. -/
theorem mappingSpaceEval_comp_lineSphereFamily :
    mappingSpaceEval Sphere2.north ∘ lineSphereFamily n =
      fun f : finiteOrthonormalFrame ℂ 2 (n + 1) ↦ mk n (f.toSphere 0) :=
  funext fun f ↦ (mappingSpaceEval_apply _ _).trans (lineSphereFamily_apply_north f)

/-- **The two-sphere of a frame is injective**: it parametrizes the projective line of the frame
once. -/
theorem lineSphereFamily_injective (f : finiteOrthonormalFrame ℂ 2 (n + 1)) :
    Function.Injective (lineSphereFamily n f) := by
  intro x y hxy
  obtain ⟨v, rfl⟩ := hopfSphere2_surjective x
  obtain ⟨w, rfl⟩ := hopfSphere2_surjective y
  rw [lineSphereFamily_apply_hopfSphere2 f v _ (coe_lineVector_apply f v),
    lineSphereFamily_apply_hopfSphere2 f w _ (coe_lineVector_apply f w), mk_eq_mk_iff] at hxy
  obtain ⟨c, hc⟩ := hxy
  rw [← lineVector_smul] at hc
  rw [← lineVector_injective f hc, hopfSphere2_smul]

/-- **The two-sphere depends only on the frame up to a unit scalar**: multiplying both vectors of
`f` by the same unit complex number `c` does not change it. So the family factors through the
quotient of the frames by the diagonal circle, the unit tangent bundle of `CPⁿ`. -/
theorem lineSphereFamily_eq_of_smul (c : sphere (0 : ℂ) 1)
    {f f' : finiteOrthonormalFrame ℂ 2 (n + 1)} (h : ∀ i, f'.val i = (c : ℂ) • f.val i) :
    lineSphereFamily n f' = lineSphereFamily n f := by
  ext1 x
  obtain ⟨v, rfl⟩ := hopfSphere2_surjective x
  rw [lineSphereFamily_apply_hopfSphere2 f' v (c • lineVector f v)
      (by simp [coe_lineVector_apply, h, WithLp.toLp_smul, smul_add, smul_comm (c : ℂ)]),
    mk_smul, lineSphereFamily_apply_hopfSphere2 f v _ (coe_lineVector_apply f v)]

/-- **The family is equivariant under the unitary group**: applying a unitary matrix `A` to the
frame moves its two-sphere by `A`. -/
theorem lineSphereFamily_unitaryMap (A : unitaryGroup (Fin (n + 1)) ℂ)
    (f : finiteOrthonormalFrame ℂ 2 (n + 1)) (x : Sphere2) :
    lineSphereFamily n (finiteOrthonormalFrame.unitaryMap A f) x = A • lineSphereFamily n f x := by
  obtain ⟨v, rfl⟩ := hopfSphere2_surjective x
  rw [lineSphereFamily_apply_hopfSphere2 f v _ (coe_lineVector_apply f v), smul_mk]
  refine lineSphereFamily_apply_hopfSphere2 _ v _ ?_
  simp [coe_lineVector_apply, Matrix.mulVec_add, Matrix.mulVec_smul]

/-- **On `CP¹`, the two-sphere of every frame is a bijection `S² → CP¹`**: an orthonormal two-frame
of `ℂ²` is a basis, so every complex line of `ℂ²` is spanned by some `a f₀ + b f₁`. -/
theorem lineSphereFamily_bijective (f : finiteOrthonormalFrame ℂ 2 2) :
    Function.Bijective (lineSphereFamily 1 f) := by
  refine ⟨lineSphereFamily_injective f, fun p ↦ ?_⟩
  induction p using ComplexProjectiveSpace.inductionOn with | h y => ?_
  -- The coordinate isometry of the frame is an injective endomorphism of `ℂ²`, hence onto.
  obtain ⟨x, hx⟩ := LinearMap.surjective_of_injective
    (f := f.property.synthesisMapIsometry.toLinearMap) f.property.synthesisMapIsometry.injective
    (y : EuclideanSpace ℂ (Fin 2))
  have hx1 : x ∈ sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 := by
    rw [mem_sphere_zero_iff_norm, ← f.property.synthesisMapIsometry.norm_map]
    exact (congrArg norm hx).trans (norm_eq_of_mem_sphere y)
  refine ⟨hopfSphere2 ⟨x, hx1⟩, ?_⟩
  rw [lineSphereFamily_apply_hopfSphere2 f _ _ (coe_lineVector_apply f _)]
  refine congrArg (mk 1) (Subtype.ext ?_)
  rw [coe_lineVector_apply]
  simpa [Orthonormal.synthesisMapIsometry_apply, Fin.sum_univ_two] using hx

/-- **The family of two-spheres through a point.** For a unit vector `u = f₀` of `ℂⁿ⁺¹`, the unit
vectors `w` of the complex orthogonal complement of `u` parametrize the unit tangent vectors of
`CPⁿ` at `[u]`; the two-sphere of the frame `(u, w)` is the projective line through `[u]` tangent
to `w`, a based map `(S², north) → (CPⁿ, [u])`. -/
def lineSphereFamilyFiber (f : finiteOrthonormalFrame ℂ 1 (n + 1)) :
    C(sphere (0 : f.complement) 1,
      BasedMap Sphere2 (ComplexProjectiveSpace n) Sphere2.north (mk n (f.toSphere 0))) where
  toFun w := ⟨lineSphereFamily n (f.snoc w),
    (lineSphereFamily_apply_north _).trans
      (congrArg (mk n) (f.toSphere_snoc_castSucc w 0))⟩
  continuous_toFun :=
    ((lineSphereFamily n).continuous.comp (finiteOrthonormalFrame.continuous_snoc f)).subtype_mk _

/-- On the fibre over `[u]`, the family of two-spheres is the two-sphere of the frame `(u, w)`. -/
@[simp]
theorem coe_lineSphereFamilyFiber_apply (f : finiteOrthonormalFrame ℂ 1 (n + 1))
    (w : sphere (0 : f.complement) 1) :
    (lineSphereFamilyFiber f w : C(Sphere2, ComplexProjectiveSpace n)) =
      lineSphereFamily n (f.snoc w) :=
  (rfl)

/-- The two-sphere through `[u]` tangent to `w` sends the south pole to `[w]`. -/
theorem lineSphereFamilyFiber_apply_south (f : finiteOrthonormalFrame ℂ 1 (n + 1))
    (w : sphere (0 : f.complement) 1) :
    (lineSphereFamilyFiber f w : C(Sphere2, ComplexProjectiveSpace n)) Sphere2.south =
      mk n ⟨w.val.val, mem_sphere_zero_iff_norm.2 (mem_sphere_zero_iff_norm.1 w.property)⟩ := by
  rw [coe_lineSphereFamilyFiber_apply, lineSphereFamily_apply_south]
  exact congrArg (mk n) (f.toSphere_snoc_last w)

/-- The two-sphere through `[u]` tangent to `w` sends `h (a, b)` to `[a u + b w]`. -/
theorem lineSphereFamilyFiber_apply_hopfSphere2 (f : finiteOrthonormalFrame ℂ 1 (n + 1))
    (w : sphere (0 : f.complement) 1) (v : sphere (0 : EuclideanSpace ℂ (Fin 2)) 1)
    (x : sphere (0 : EuclideanSpace ℂ (Fin (n + 1))) 1)
    (hx : (x : EuclideanSpace ℂ (Fin (n + 1))) =
      (v : EuclideanSpace ℂ (Fin 2)) 0 • WithLp.toLp 2 (f.val 0) +
        (v : EuclideanSpace ℂ (Fin 2)) 1 • (w : EuclideanSpace ℂ (Fin (n + 1)))) :
    (lineSphereFamilyFiber f w : C(Sphere2, ComplexProjectiveSpace n)) (hopfSphere2 v) =
      mk n x := by
  rw [coe_lineSphereFamilyFiber_apply]
  refine lineSphereFamily_apply_hopfSphere2 _ v x ?_
  rw [hx]
  congr 2
  · simpa using (congrArg (WithLp.toLp 2) (f.snoc_castSucc w 0)).symm
  · simpa using (congrArg (WithLp.toLp 2) (f.snoc_last w)).symm

end Line

end ComplexProjectiveSpace

end TauCeti
