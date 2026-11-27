/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Configuration
public import TauCeti.LinearAlgebra.CrossProduct
public import TauCeti.Topology.ComplexProjectiveSpace.Line.Basic
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization
public import TauCeti.Topology.Grassmannian.Plucker

/-!
# The moduli space of lines of `CP²` is the dual projective plane

The standard lines of `CP²` are the projective lines `σ_f : S² → CP²`, `h (a, b) ↦ [a f₀ + b f₁]`,
of the orthonormal two-frames `f = (f₀, f₁)` of `ℂ³`
(`TauCeti.ComplexProjectiveSpace.lineSphereFamily`): the linear embeddings
`[a : b] ↦ [a f₀ + b f₁]` of `CP¹`, read through `CP¹ ≃ₜ S²`. This file identifies the space of
these lines, as subsets of `CP²`, with the dual projective plane, and their incidence with points
with the incidence of the projective plane over `ℂ`.

Points of the dual plane are modelled, as in Mathlib's projective plane over a field
(`Configuration.ofField`), by the same projectivization `ℙ ℂ (Fin 3 → ℂ)`: a point `[w]` stands
for the line `{[v] | w ⬝ᵥ v = 0}` of the bilinear dot product (`Projectivization.orthogonal`).
`CP²` is read in `ℙ ℂ (Fin 3 → ℂ)` through
`TauCeti.ComplexProjectiveSpace.homeomorphProjectivization`.

* **The dual point of a line.** The line of `f` lies in the plane spanned by `f₀` and `f₁`, which
  is the plane `{v | (f₀ × f₁) ⬝ᵥ v = 0}`: the dual point of `f` is `[f₀ × f₁]`
  (`TauCeti.ComplexProjectiveSpace.dualPoint`), Mathlib's cross product `[f₀] × [f₁]` of
  projective points (`TauCeti.ComplexProjectiveSpace.dualPoint_eq_cross`): the only point of the
  dual plane orthogonal to both `[f₀]` and `[f₁]`
  (`TauCeti.ComplexProjectiveSpace.orthogonal_dualPoint`,
  `TauCeti.ComplexProjectiveSpace.dualPoint_eq_of_orthogonal`).
  A point `[v]` of `CP²` lies on `σ_f` exactly when `v ⬝ᵥ (f₀ × f₁) = 0`
  (`TauCeti.ComplexProjectiveSpace.mem_range_lineSphereFamily_iff`): a vector orthogonal to
  `f₀ × f₁` is a combination `a f₀ + b f₁`, and if it has norm one then so does `(a, b)`, since
  the frame is orthonormal.
* **Lines and dual points.** Two frames have the same line exactly when they have the same dual
  point (`TauCeti.ComplexProjectiveSpace.range_lineSphereFamily_eq_iff`): the distinct points `[f₀]`
  and `[f₁]` lie on both lines, and two distinct points lie on at most one line of the projective
  plane. Every point `[w]` of the dual plane is the dual point of a frame
  (`TauCeti.ComplexProjectiveSpace.dualPoint_surjective`): take an orthonormal frame spanning the
  plane `{v | w ⬝ᵥ v = 0}`. The dual point depends continuously on the frame.
* **The line moduli.** The moduli space of standard lines
  (`TauCeti.ComplexProjectiveSpace.LineModuli`) is the Grassmannian of planes of `ℂ³`, compact and
  Hausdorff, with the quotient topology from the orthonormal frames: the line of `f` is the plane
  spanned by `f`. Two frames span the same plane exactly when they have the same dual point, so
  the dual point descends to a homeomorphism onto the dual plane
  (`TauCeti.ComplexProjectiveSpace.LineModuli.dualHomeomorph`), a continuous bijection from a
  compact space to a Hausdorff space.
* **Incidence.** A line `L` is the set of points `p` of `CP²` orthogonal to the dual point of `L`
  (`TauCeti.ComplexProjectiveSpace.LineModuli.mem_iff`); for the line of `f` these are the values
  of `σ_f` (`TauCeti.ComplexProjectiveSpace.LineModuli.coe_mk`). So `CP²` with its standard lines
  is a projective plane (`Configuration.ProjectivePlane`), isomorphic to the plane over `ℂ`: two
  distinct points lie on exactly one standard line (`Configuration.HasLines.existsUnique_line`),
  and two distinct standard lines meet in exactly one point
  (`Configuration.HasPoints.existsUnique_point`). The incidence correspondence
  `{(p, L) | p ∈ L} ⊆ CP² × LineModuli` is the image of the marked lines `(f, x) ↦ (σ_f x, [f])`
  (`TauCeti.ComplexProjectiveSpace.LineModuli.range_lineSphereFamily_prod_mk`), hence compact
  (`TauCeti.ComplexProjectiveSpace.LineModuli.isCompact_setOf_mem`).

The moduli space here consists of the images of the standard lines. That every holomorphic sphere
of degree one in `CP²` for the standard complex structure is such a line, up to reparametrization,
is not part of this file.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Chapter 9 (Gromov's characterization of `CP²` by the lines through two points and the
  intersection point of two lines).
* The projective plane over a field, with the dual points as lines, is Mathlib's
  `Configuration.ofField` instance, in `Mathlib.Combinatorics.Configuration`; the incidence
  structure on `CP²` is transported from it.
-/

public section

noncomputable section

open Metric Matrix Projectivization Set

open scoped LinearAlgebra.Projectivization

namespace TauCeti

namespace ComplexProjectiveSpace

/-! ### The dual point of a line -/

section DualPoint

/-- **The dual point of the line of a frame**: the point `[f₀ × f₁]` of the dual projective plane
`ℙ ℂ (Fin 3 → ℂ)`, whose points `[w]` stand for the lines `{[v] | w ⬝ᵥ v = 0}` of `CP²`. -/
def dualPoint (f : finiteOrthonormalFrame ℂ 2 3) : ℙ ℂ (Fin 3 → ℂ) :=
  Projectivization.mk ℂ (f.val 0 ⨯₃ f.val 1) f.crossProduct_ne_zero

/-- The dual point of `f` is the class of `f₀ × f₁`. -/
theorem dualPoint_def (f : finiteOrthonormalFrame ℂ 2 3) :
    dualPoint f = Projectivization.mk ℂ (f.val 0 ⨯₃ f.val 1) f.crossProduct_ne_zero :=
  (rfl)

/-- The point `[fᵢ]` of `CP²`, read in `ℙ ℂ (Fin 3 → ℂ)`, is the class of the vector `fᵢ`. -/
private theorem homeomorphProjectivization_mk_toSphere (f : finiteOrthonormalFrame ℂ 2 3)
    (i : Fin 2) :
    homeomorphProjectivization 2 (mk 2 (f.toSphere i)) =
      Projectivization.mk ℂ (f.val i) (f.val_ne_zero i) := by
  simp

private theorem mk_val_zero_ne_mk_val_one (f : finiteOrthonormalFrame ℂ 2 3) :
    Projectivization.mk ℂ (f.val 0) (f.val_ne_zero 0) ≠
      Projectivization.mk ℂ (f.val 1) (f.val_ne_zero 1) := by
  rw [Ne, mk_eq_mk_iff_crossProduct_eq_zero]
  exact f.crossProduct_ne_zero

/-- The dual point of `f` is the cross product `[f₀] × [f₁]` of the points `[f₀]` and `[f₁]` of the
projective plane, the line through them in `Configuration.ofField`. -/
theorem dualPoint_eq_cross [DecidableEq ℂ] (f : finiteOrthonormalFrame ℂ 2 3) :
    dualPoint f = cross (Projectivization.mk ℂ (f.val 0) (f.val_ne_zero 0))
      (Projectivization.mk ℂ (f.val 1) (f.val_ne_zero 1)) :=
  (cross_mk_of_ne _ _ (mk_val_zero_ne_mk_val_one f)).symm

/-- The points `[f₀]` and `[f₁]` of the projective plane are orthogonal to the dual point of `f`:
both lie on the line it stands for. -/
theorem orthogonal_dualPoint (f : finiteOrthonormalFrame ℂ 2 3) (i : Fin 2) :
    (Projectivization.mk ℂ (f.val i) (f.val_ne_zero i)).orthogonal (dualPoint f) := by
  classical
  rw [dualPoint_eq_cross]
  fin_cases i
  · exact orthogonal_cross_left (mk_val_zero_ne_mk_val_one f)
  · exact orthogonal_cross_right (mk_val_zero_ne_mk_val_one f)

/-- The dual point of `f` is the only point of the dual plane orthogonal to both `[f₀]` and
`[f₁]`: these are distinct points, and two distinct points lie on at most one line. -/
theorem dualPoint_eq_of_orthogonal {f : finiteOrthonormalFrame ℂ 2 3}
    {w : ℙ ℂ (Fin 3 → ℂ)}
    (h₀ : (Projectivization.mk ℂ (f.val 0) (f.val_ne_zero 0)).orthogonal w)
    (h₁ : (Projectivization.mk ℂ (f.val 1) (f.val_ne_zero 1)).orthogonal w) :
    dualPoint f = w :=
  (Configuration.ofField.eq_or_eq_of_orthogonal (orthogonal_dualPoint f 0)
    (orthogonal_dualPoint f 1) h₀ h₁).resolve_left (mk_val_zero_ne_mk_val_one f)

/-- A nonzero vector `v` lies in the plane spanned by a frame `g` exactly when `[v]` is
orthogonal to the dual point of `g`. -/
private theorem mem_span_range_iff_orthogonal (g : finiteOrthonormalFrame ℂ 2 3)
    {v : Fin 3 → ℂ} (hv : v ≠ 0) :
    v ∈ Submodule.span ℂ (range g.val) ↔
      (Projectivization.mk ℂ v hv).orthogonal (dualPoint g) := by
  have hg : range g.val = {g.val 0, g.val 1} := by
    ext v
    simp [Fin.exists_fin_two, eq_comm]
  rw [dualPoint_def, orthogonal_mk,
    triple_product_eq_zero_iff_mem_span_pair g.linearIndependent_val_pair, hg]

/-- A point `[y]` of `CP²` lies on the two-sphere `σ_f` exactly when `y` lies in the plane spanned
by `f₀` and `f₁`. -/
private theorem mk_mem_range_lineSphereFamily_iff (f : finiteOrthonormalFrame ℂ 2 3)
    (y : sphere (0 : EuclideanSpace ℂ (Fin 3)) 1) :
    mk 2 y ∈ range (lineSphereFamily 2 f) ↔
      WithLp.ofLp (y : EuclideanSpace ℂ (Fin 3)) ∈ Submodule.span ℂ {f.val 0, f.val 1} := by
  constructor
  · rintro ⟨x, hx⟩
    obtain ⟨v, rfl⟩ := hopfSphere2_surjective x
    rw [lineSphereFamily_apply_hopfSphere2 f v _ (coe_lineVector_apply f v), mk_eq_mk_iff] at hx
    obtain ⟨c, hc⟩ := hx
    have h2 : (c : ℂ) • WithLp.ofLp (y : EuclideanSpace ℂ (Fin 3)) =
        WithLp.ofLp (lineVector f v : EuclideanSpace ℂ (Fin 3)) := by
      simpa using congrArg (fun z : sphere (0 : EuclideanSpace ℂ (Fin 3)) 1 ↦
        WithLp.ofLp (z : EuclideanSpace ℂ (Fin 3))) hc
    refine (Submodule.smul_mem_iff _ (ne_zero_of_mem_sphere one_ne_zero c)).1 ?_
    rw [h2]
    simp only [coe_lineVector_apply, WithLp.ofLp_add, WithLp.ofLp_smul]
    refine Submodule.add_mem _ ?_ ?_
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
    · exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp))
  · intro hy
    obtain ⟨a, b, hab⟩ := Submodule.mem_span_pair.1 hy
    set u : EuclideanSpace ℂ (Fin 2) := WithLp.toLp 2 ![a, b]
    have hu : f.property.synthesisMapIsometry u = y := by
      rw [Orthonormal.synthesisMapIsometry_apply, Fin.sum_univ_two]
      apply (WithLp.linearEquiv 2 ℂ (Fin 3 → ℂ)).injective
      simpa [u] using hab
    have hu1 : u ∈ sphere (0 : EuclideanSpace ℂ (Fin 2)) 1 := by
      rw [mem_sphere_zero_iff_norm, ← f.property.synthesisMapIsometry.norm_map, hu]
      exact norm_eq_of_mem_sphere y
    refine ⟨hopfSphere2 ⟨u, hu1⟩, lineSphereFamily_apply_hopfSphere2 f _ y ?_⟩
    rw [← hu, Orthonormal.synthesisMapIsometry_apply, Fin.sum_univ_two]

/-- **The standard line of a frame is the line of its dual point**: a point of `CP²` lies on the
two-sphere `σ_f` of an orthonormal two-frame `f` of `ℂ³` exactly when it is orthogonal to
`f₀ × f₁` for the bilinear dot product. -/
theorem mem_range_lineSphereFamily_iff (f : finiteOrthonormalFrame ℂ 2 3)
    (p : ComplexProjectiveSpace 2) :
    p ∈ range (lineSphereFamily 2 f) ↔
      (homeomorphProjectivization 2 p).orthogonal (dualPoint f) := by
  induction p using ComplexProjectiveSpace.inductionOn with | h y => ?_
  rw [homeomorphProjectivization_mk, dualPoint_def, orthogonal_mk,
    triple_product_eq_zero_iff_mem_span_pair f.linearIndependent_val_pair,
    mk_mem_range_lineSphereFamily_iff]

/-- If every point of the standard line of `f` is orthogonal to `w`, then `w` is the dual point
of `f`: the line contains the distinct points `[f₀]` and `[f₁]`. -/
private theorem dualPoint_eq_of_range_subset {f : finiteOrthonormalFrame ℂ 2 3}
    {w : ℙ ℂ (Fin 3 → ℂ)}
    (h : range (lineSphereFamily 2 f) ⊆ {p | (homeomorphProjectivization 2 p).orthogonal w}) :
    dualPoint f = w := by
  have hmem (i : Fin 2) : (Projectivization.mk ℂ (f.val i) (f.val_ne_zero i)).orthogonal w := by
    rw [← homeomorphProjectivization_mk_toSphere]
    refine h ((mem_range_lineSphereFamily_iff f _).2 ?_)
    rw [homeomorphProjectivization_mk_toSphere]
    exact orthogonal_dualPoint f i
  exact dualPoint_eq_of_orthogonal (hmem 0) (hmem 1)

/-- **Two standard lines coincide exactly when their dual points do.** -/
theorem range_lineSphereFamily_eq_iff {f g : finiteOrthonormalFrame ℂ 2 3} :
    range (lineSphereFamily 2 f) = range (lineSphereFamily 2 g) ↔ dualPoint f = dualPoint g := by
  refine ⟨fun h ↦ dualPoint_eq_of_range_subset fun p hp ↦ ?_, fun h ↦ ?_⟩
  · exact (mem_range_lineSphereFamily_iff g p).1 (h ▸ hp)
  · ext p
    rw [mem_range_lineSphereFamily_iff, mem_range_lineSphereFamily_iff, h]

/-- **Every line of the projective plane is a standard line**: every point of the dual plane is
the dual point of an orthonormal two-frame of `ℂ³`. -/
theorem dualPoint_surjective : Function.Surjective dualPoint := by
  intro w
  induction w using Projectivization.ind with | h w hw => ?_
  -- The vectors `v` with `w ⬝ᵥ v = 0` form a plane `K`, spanned by an orthonormal frame.
  set K := LinearMap.ker (dotProductEquiv ℂ (Fin 3) w)
  have hK : Module.finrank ℂ K = 2 := by
    have h : Module.finrank ℂ K + 1 = Module.finrank ℂ (Fin 3 → ℂ) :=
      Module.Dual.finrank_ker_add_one_of_ne_zero ((dotProductEquiv ℂ (Fin 3)).map_ne_zero_iff.2 hw)
    rw [Module.finrank_fin_fun] at h
    omega
  obtain ⟨f, hf⟩ :=
    finiteGrassmannian.frameSpan_toFullRankFrame_surjective (⟨K, hK⟩ : finiteGrassmannian ℂ 2 3)
  have hfK (i : Fin 2) :
      (Projectivization.mk ℂ (f.val i) (f.val_ne_zero i)).orthogonal
        (Projectivization.mk ℂ w hw) := by
    have hi : f.val i ∈ K := by
      have h : Submodule.span ℂ (range f.val) = K := by
        simpa using congrArg Subtype.val hf
      exact h ▸ Submodule.subset_span (mem_range_self i)
    rw [orthogonal_mk, dotProduct_comm]
    simpa [K] using hi
  exact ⟨f, dualPoint_eq_of_orthogonal (hfK 0) (hfK 1)⟩

/-- The dual point of the line of a frame depends continuously on the frame. -/
@[fun_prop]
theorem continuous_dualPoint : Continuous dualPoint := by
  refine Projectivization.continuous_mk ?_ finiteOrthonormalFrame.crossProduct_ne_zero
  have h (i : Fin 2) (k : Fin 3) : Continuous fun f : finiteOrthonormalFrame ℂ 2 3 ↦ f.val i k :=
    (continuous_apply k).comp ((continuous_apply i).comp continuous_subtypeVal)
  simp only [cross_apply]
  refine .matrixVecCons ?_ (.matrixVecCons ?_ (.matrixVecCons ?_ continuous_const)) <;>
    exact ((h _ _).mul (h _ _)).sub ((h _ _).mul (h _ _))

end DualPoint

/-! ### The moduli space of lines -/

/-- **The moduli space of the standard lines of `CP²`**: the Grassmannian of complex planes of
`ℂ³`, the plane spanned by an orthonormal two-frame `f` standing for the standard line `σ_f`. It
carries the quotient topology from the orthonormal two-frames (`LineModuli.isQuotientMap_mk`). -/
def LineModuli : Type :=
  finiteGrassmannian ℂ 2 3

namespace LineModuli

instance : TopologicalSpace LineModuli :=
  inferInstanceAs (TopologicalSpace (finiteGrassmannian ℂ 2 3))

instance : CompactSpace LineModuli :=
  inferInstanceAs (CompactSpace (finiteGrassmannian ℂ 2 3))

instance : T2Space LineModuli :=
  inferInstanceAs (T2Space (finiteGrassmannian ℂ 2 3))

/-- The standard line of an orthonormal two-frame of `ℂ³`: the plane spanned by the frame. -/
def mk (f : finiteOrthonormalFrame ℂ 2 3) : LineModuli :=
  finiteGrassmannian.frameSpan f.toFullRankFrame

/-- Every standard line is the line of a frame. -/
theorem mk_surjective : Function.Surjective mk :=
  finiteGrassmannian.frameSpan_toFullRankFrame_surjective

/-- The line moduli carries the quotient topology from the orthonormal two-frames. -/
theorem isQuotientMap_mk : Topology.IsQuotientMap mk :=
  finiteGrassmannian.isQuotientMap_frameSpan_toFullRankFrame

/-- The standard line of a frame depends continuously on the frame. -/
@[fun_prop]
theorem continuous_mk : Continuous mk :=
  isQuotientMap_mk.continuous

/-- Two frames span the same plane exactly when they have the same dual point. -/
private theorem mk_eq_mk_iff_dualPoint_eq {f g : finiteOrthonormalFrame ℂ 2 3} :
    mk f = mk g ↔ dualPoint f = dualPoint g := by
  have hspan (f : finiteOrthonormalFrame ℂ 2 3) :
      (mk f : finiteGrassmannian ℂ 2 3).val = Submodule.span ℂ (range f.val) := by
    rw [← finiteOrthonormalFrame.coe_toFullRankFrame f]
    exact finiteGrassmannian.coe_frameSpan f.toFullRankFrame
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · have hmem (i : Fin 2) : (Projectivization.mk ℂ (f.val i) (f.val_ne_zero i)).orthogonal
        (dualPoint g) := by
      rw [← mem_span_range_iff_orthogonal, ← hspan, ← h, hspan]
      exact Submodule.subset_span (mem_range_self i)
    exact dualPoint_eq_of_orthogonal (hmem 0) (hmem 1)
  · -- The plane of `f` lies in the plane of `g`, and both have dimension two.
    refine Subtype.ext (Submodule.eq_of_le_of_finrank_eq ?_
      ((mk f).property.trans (mk g).property.symm))
    rw [hspan, hspan, Submodule.span_le]
    rintro _ ⟨i, rfl⟩
    rw [SetLike.mem_coe, mem_span_range_iff_orthogonal _ (f.val_ne_zero i), ← h]
    exact orthogonal_dualPoint f i

/-- The dual point, descended to the line moduli. -/
private def dualMap : C(LineModuli, ℙ ℂ (Fin 3 → ℂ)) :=
  isQuotientMap_mk.lift (f := ⟨mk, continuous_mk⟩) ⟨dualPoint, continuous_dualPoint⟩
    fun _ _ h ↦ mk_eq_mk_iff_dualPoint_eq.1 h

private theorem dualMap_mk (f : finiteOrthonormalFrame ℂ 2 3) : dualMap (mk f) = dualPoint f :=
  DFunLike.congr_fun (isQuotientMap_mk.lift_comp (f := ⟨mk, continuous_mk⟩)
    ⟨dualPoint, continuous_dualPoint⟩ fun _ _ h ↦ mk_eq_mk_iff_dualPoint_eq.1 h) f

/-- **The line moduli is the dual projective plane**: the homeomorphism from the moduli space of
standard lines of `CP²` to `ℙ ℂ (Fin 3 → ℂ)` sending the line of a frame `f` to `[f₀ × f₁]`. -/
def dualHomeomorph : LineModuli ≃ₜ ℙ ℂ (Fin 3 → ℂ) :=
  dualMap.continuous.homeoOfEquivCompactToT2 (f := Equiv.ofBijective dualMap ⟨by
    intro L L' h
    obtain ⟨f, rfl⟩ := mk_surjective L
    obtain ⟨g, rfl⟩ := mk_surjective L'
    rw [dualMap_mk, dualMap_mk] at h
    exact mk_eq_mk_iff_dualPoint_eq.2 h, by
    intro w
    obtain ⟨f, rfl⟩ := dualPoint_surjective w
    exact ⟨mk f, dualMap_mk f⟩⟩)

/-- The dual point of the standard line of `f` is `[f₀ × f₁]`. -/
@[simp]
theorem dualHomeomorph_mk (f : finiteOrthonormalFrame ℂ 2 3) :
    dualHomeomorph (mk f) = dualPoint f :=
  dualMap_mk f

/-- The standard line with dual point `[f₀ × f₁]` is the standard line of `f`. -/
@[simp]
theorem dualHomeomorph_symm_dualPoint (f : finiteOrthonormalFrame ℂ 2 3) :
    dualHomeomorph.symm (dualPoint f) = mk f :=
  dualHomeomorph.symm_apply_eq.2 (dualHomeomorph_mk f).symm

/-- A line of `CP²` is the set of its points: the points orthogonal to its dual point. -/
instance : SetLike LineModuli (ComplexProjectiveSpace 2) where
  coe L := {p | (homeomorphProjectivization 2 p).orthogonal (dualHomeomorph L)}
  coe_injective := by
    intro L L' h
    simp only at h
    obtain ⟨f, rfl⟩ := mk_surjective L
    -- The points of the line of `f` also lie on `L'`.
    refine dualHomeomorph.injective ((dualHomeomorph_mk f).trans
      (dualPoint_eq_of_range_subset fun p hp ↦ ?_))
    rw [← h, mem_ofPred_eq, dualHomeomorph_mk]
    exact (mem_range_lineSphereFamily_iff f p).1 hp

/-- **Point-line incidence in `CP²`**: a point `p` lies on a standard line `L` exactly when `p` is
orthogonal to the dual point of `L` for the bilinear dot product. -/
theorem mem_iff (p : ComplexProjectiveSpace 2) (L : LineModuli) :
    p ∈ L ↔ (homeomorphProjectivization 2 p).orthogonal (dualHomeomorph L) :=
  Iff.rfl

/-- The points of the standard line of `f` are the values of its two-sphere `σ_f`. -/
@[simp]
theorem coe_mk (f : finiteOrthonormalFrame ℂ 2 3) :
    (mk f : Set (ComplexProjectiveSpace 2)) = range (lineSphereFamily 2 f) := by
  ext p
  rw [SetLike.mem_coe, mem_iff, dualHomeomorph_mk, mem_range_lineSphereFamily_iff]

/-- A point lies on the standard line of `f` exactly when it is a value of its two-sphere `σ_f`. -/
@[simp]
theorem mem_mk {f : finiteOrthonormalFrame ℂ 2 3} {p : ComplexProjectiveSpace 2} :
    p ∈ mk f ↔ p ∈ range (lineSphereFamily 2 f) := by
  rw [← SetLike.mem_coe, coe_mk]

/-- Two frames have the same standard line exactly when their two-spheres have the same image. -/
theorem mk_eq_mk_iff {f g : finiteOrthonormalFrame ℂ 2 3} :
    mk f = mk g ↔ range (lineSphereFamily 2 f) = range (lineSphereFamily 2 g) := by
  rw [← SetLike.coe_set_eq, coe_mk, coe_mk]

/-- **The incidence correspondence is swept out by the marked lines**: the pairs `(p, L)` of a point
of `CP²` and a standard line through it are the pairs `(σ_f x, [f])` of a frame `f` and a point
`x` of the two-sphere. -/
theorem range_lineSphereFamily_prod_mk :
    range (fun q : finiteOrthonormalFrame ℂ 2 3 × Sphere2 ↦ (lineSphereFamily 2 q.1 q.2, mk q.1)) =
      {x : ComplexProjectiveSpace 2 × LineModuli | x.1 ∈ x.2} := by
  ext ⟨p, L⟩
  obtain ⟨f, rfl⟩ := mk_surjective L
  refine ⟨?_, fun h ↦ ?_⟩
  · rintro ⟨⟨g, x⟩, h⟩
    simp only [Prod.mk.injEq] at h
    obtain ⟨rfl, hg⟩ := h
    rw [mem_ofPred_eq, ← hg, mem_mk]
    exact mem_range_self x
  · rw [mem_ofPred_eq, mem_mk] at h
    obtain ⟨x, rfl⟩ := h
    exact ⟨(f, x), rfl⟩

/-- **The incidence correspondence of `CP²` is compact**: it is the image of the compact space of
marked frames under a continuous map. -/
theorem isCompact_setOf_mem :
    IsCompact {x : ComplexProjectiveSpace 2 × LineModuli | x.1 ∈ x.2} := by
  rw [← range_lineSphereFamily_prod_mk]
  refine isCompact_range (Continuous.prodMk ?_ (continuous_mk.comp continuous_fst))
  exact continuous_eval.comp ((lineSphereFamily 2).continuous.prodMap continuous_id)

/-- **`CP²` with its standard lines is a projective plane**: two distinct points lie on exactly
one standard line (`Configuration.HasLines.existsUnique_line`), and two distinct standard lines
meet in exactly one point (`Configuration.HasPoints.existsUnique_point`). -/
instance : Configuration.ProjectivePlane (ComplexProjectiveSpace 2) LineModuli := by
  classical
  -- Transport the projective plane `ℙ ℂ (Fin 3 → ℂ)`, with the dual points as lines.
  set e : ComplexProjectiveSpace 2 ≃ₜ ℙ ℂ (Fin 3 → ℂ) := homeomorphProjectivization 2
  set d := dualHomeomorph
  have he (p : ComplexProjectiveSpace 2) (L : LineModuli) : p ∈ L ↔ e p ∈ d L := by
    rw [mem_iff, Configuration.ofField.mem_iff]
  have he' (v : ℙ ℂ (Fin 3 → ℂ)) (L : LineModuli) : e.symm v ∈ L ↔ v ∈ d L := by
    rw [he, e.apply_symm_apply]
  have hd' (p : ComplexProjectiveSpace 2) (w : ℙ ℂ (Fin 3 → ℂ)) : p ∈ d.symm w ↔ e p ∈ w := by
    rw [he, d.apply_symm_apply]
  exact
  { exists_point := fun L ↦ by
      obtain ⟨v, hv⟩ := Configuration.Nondegenerate.exists_point (P := ℙ ℂ (Fin 3 → ℂ)) (d L)
      exact ⟨e.symm v, by rwa [he']⟩
    exists_line := fun p ↦ by
      obtain ⟨w, hw⟩ := Configuration.Nondegenerate.exists_line (L := ℙ ℂ (Fin 3 → ℂ)) (e p)
      exact ⟨d.symm w, by rwa [hd']⟩
    eq_or_eq := fun h₁ h₂ h₃ h₄ ↦ by
      rw [he] at h₁ h₂ h₃ h₄
      exact (Configuration.Nondegenerate.eq_or_eq h₁ h₂ h₃ h₄).imp (fun h ↦ e.injective h)
        fun h ↦ d.injective h
    mkPoint := fun h ↦ e.symm (Configuration.HasPoints.mkPoint (d.injective.ne h))
    mkPoint_ax := fun h ↦ by
      rw [he', he']
      exact Configuration.HasPoints.mkPoint_ax (d.injective.ne h)
    mkLine := fun h ↦ d.symm (Configuration.HasLines.mkLine (e.injective.ne h))
    mkLine_ax := fun h ↦ by
      rw [hd', hd']
      exact Configuration.HasLines.mkLine_ax (e.injective.ne h)
    exists_config := by
      obtain ⟨p₁, p₂, p₃, l₁, l₂, l₃, h⟩ :=
        Configuration.ProjectivePlane.exists_config (P := ℙ ℂ (Fin 3 → ℂ))
          (L := ℙ ℂ (Fin 3 → ℂ))
      refine ⟨e.symm p₁, e.symm p₂, e.symm p₃, d.symm l₁, d.symm l₂, d.symm l₃, ?_⟩
      simp only [hd', e.apply_symm_apply]
      exact h }

end LineModuli

end ComplexProjectiveSpace

end TauCeti
