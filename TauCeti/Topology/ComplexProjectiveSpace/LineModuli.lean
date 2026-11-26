/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Combinatorics.Configuration
public import TauCeti.LinearAlgebra.CrossProduct
public import TauCeti.Topology.ComplexProjectiveSpace.Line
public import TauCeti.Topology.ComplexProjectiveSpace.Projectivization

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
  (`TauCeti.ComplexProjectiveSpace.dualPoint`). A point `[v]` of `CP²` lies on `σ_f` exactly when
  `v ⬝ᵥ (f₀ × f₁) = 0` (`TauCeti.ComplexProjectiveSpace.mem_range_lineSphereFamily_iff`): a vector
  orthogonal to `f₀ × f₁` is a combination `a f₀ + b f₁`, and if it has norm one then so does
  `(a, b)`, since the frame is orthonormal.
* **Lines and dual points.** Two frames have the same line exactly when they have the same dual
  point (`TauCeti.ComplexProjectiveSpace.range_lineSphereFamily_eq_iff`): the distinct points `[f₀]`
  and `[f₁]` lie on both lines, and two distinct points lie on at most one line of the projective
  plane. Every point `[w]` of the dual plane is the dual point of a frame
  (`TauCeti.ComplexProjectiveSpace.dualPoint_surjective`): orthonormalize a basis of the plane
  `{v | w ⬝ᵥ v = 0}`. The dual point depends continuously on the frame.
* **The line moduli.** The moduli space of standard lines
  (`TauCeti.ComplexProjectiveSpace.LineModuli`) is the quotient of the compact space of frames by
  the relation of having the same line, a type of subsets of `CP²`. The dual point descends to a
  homeomorphism onto the dual plane (`TauCeti.ComplexProjectiveSpace.LineModuli.dualHomeomorph`),
  a continuous bijection from a compact space to a Hausdorff space.
* **Incidence.** A point `p` lies on a line `L` exactly when `p` is orthogonal to the dual point of
  `L` (`TauCeti.ComplexProjectiveSpace.LineModuli.mem_iff`). So `CP²` with its standard lines is a
  projective plane (`Configuration.ProjectivePlane`), isomorphic to the plane over `ℂ`: two
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

namespace finiteOrthonormalFrame

/-- **The two vectors of an orthonormal two-frame of `𝕜³` have a nonzero cross product**, since
they are linearly independent. -/
theorem crossProduct_ne_zero {𝕜 : Type*} [RCLike 𝕜] (f : finiteOrthonormalFrame 𝕜 2 3) :
    f.val 0 ⨯₃ f.val 1 ≠ 0 := by
  rw [crossProduct_ne_zero_iff_linearIndependent]
  have h := f.toFullRankFrame.property
  rw [coe_toFullRankFrame] at h
  convert h using 1
  ext i : 1
  fin_cases i <;> rfl

end finiteOrthonormalFrame

namespace ComplexProjectiveSpace

/-! ### The dual point of a line -/

section DualPoint

private theorem linearIndependent_val_pair (f : finiteOrthonormalFrame ℂ 2 3) :
    LinearIndependent ℂ ![f.val 0, f.val 1] :=
  crossProduct_ne_zero_iff_linearIndependent.1 f.crossProduct_ne_zero

private theorem val_ne_zero (f : finiteOrthonormalFrame ℂ 2 3) (i : Fin 2) : f.val i ≠ 0 := by
  simpa using f.toFullRankFrame.property.ne_zero i

/-- **The dual point of the line of a frame**: the point `[f₀ × f₁]` of the dual projective plane
`ℙ ℂ (Fin 3 → ℂ)`, whose points `[w]` stand for the lines `{[v] | w ⬝ᵥ v = 0}` of `CP²`. -/
def dualPoint (f : finiteOrthonormalFrame ℂ 2 3) : ℙ ℂ (Fin 3 → ℂ) :=
  Projectivization.mk ℂ (f.val 0 ⨯₃ f.val 1) f.crossProduct_ne_zero

/-- The point `[fᵢ]` of `CP²`, read in `ℙ ℂ (Fin 3 → ℂ)`, is the class of the vector `fᵢ`. -/
private theorem homeomorphProjectivization_mk_toSphere (f : finiteOrthonormalFrame ℂ 2 3)
    (i : Fin 2) :
    homeomorphProjectivization 2 (mk 2 (f.toSphere i)) =
      Projectivization.mk ℂ (f.val i) (val_ne_zero f i) := by
  simp

private theorem orthogonal_dualPoint (f : finiteOrthonormalFrame ℂ 2 3) (i : Fin 2) :
    (Projectivization.mk ℂ (f.val i) (val_ne_zero f i)).orthogonal (dualPoint f) := by
  rw [dualPoint, orthogonal_mk]
  fin_cases i
  · exact dot_self_cross _ _
  · exact dot_cross_self _ _

private theorem mk_val_zero_ne_mk_val_one (f : finiteOrthonormalFrame ℂ 2 3) :
    Projectivization.mk ℂ (f.val 0) (val_ne_zero f 0) ≠
      Projectivization.mk ℂ (f.val 1) (val_ne_zero f 1) := by
  rw [Ne, mk_eq_mk_iff_crossProduct_eq_zero]
  exact f.crossProduct_ne_zero

/-- **The standard line of a frame is the line of its dual point**: a point of `CP²` lies on the
two-sphere `σ_f` of an orthonormal two-frame `f` of `ℂ³` exactly when it is orthogonal to
`f₀ × f₁` for the bilinear dot product. -/
theorem mem_range_lineSphereFamily_iff (f : finiteOrthonormalFrame ℂ 2 3)
    (p : ComplexProjectiveSpace 2) :
    p ∈ range (lineSphereFamily 2 f) ↔
      (homeomorphProjectivization 2 p).orthogonal (dualPoint f) := by
  induction p using ComplexProjectiveSpace.inductionOn with | h y => ?_
  rw [homeomorphProjectivization_mk, dualPoint, orthogonal_mk,
    triple_product_eq_zero_iff_mem_span_pair (linearIndependent_val_pair f)]
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
    rw [h2, coe_lineVector_apply, WithLp.ofLp_add, WithLp.ofLp_smul, WithLp.ofLp_smul,
      WithLp.ofLp_toLp, WithLp.ofLp_toLp]
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

/-- **Two standard lines coincide exactly when their dual points do.** -/
theorem range_lineSphereFamily_eq_iff {f g : finiteOrthonormalFrame ℂ 2 3} :
    range (lineSphereFamily 2 f) = range (lineSphereFamily 2 g) ↔ dualPoint f = dualPoint g := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- The points `[f₀]` and `[f₁]` are distinct, and both lie on the two lines.
    have hmem (i : Fin 2) : (Projectivization.mk ℂ (f.val i) (val_ne_zero f i)).orthogonal
        (dualPoint g) := by
      rw [← homeomorphProjectivization_mk_toSphere, ← mem_range_lineSphereFamily_iff, ← h,
        mem_range_lineSphereFamily_iff, homeomorphProjectivization_mk_toSphere]
      exact orthogonal_dualPoint f i
    exact (Configuration.ofField.eq_or_eq_of_orthogonal (orthogonal_dualPoint f 0)
      (orthogonal_dualPoint f 1) (hmem 0) (hmem 1)).resolve_left (mk_val_zero_ne_mk_val_one f)
  · ext p
    rw [mem_range_lineSphereFamily_iff, mem_range_lineSphereFamily_iff, h]

/-- **Every line of the projective plane is a standard line**: every point of the dual plane is
the dual point of an orthonormal two-frame of `ℂ³`. -/
theorem dualPoint_surjective : Function.Surjective dualPoint := by
  intro w
  induction w using Projectivization.ind with | h w hw => ?_
  -- The vectors `v` with `w ⬝ᵥ v = 0` form a plane `K`; orthonormalize a basis of it.
  set K := LinearMap.ker (dotProductEquiv ℂ (Fin 3) w)
  have hK : Module.finrank ℂ K = 2 := by
    have h : Module.finrank ℂ K + 1 = Module.finrank ℂ (Fin 3 → ℂ) :=
      Module.Dual.finrank_ker_add_one_of_ne_zero ((dotProductEquiv ℂ (Fin 3)).map_ne_zero_iff.2 hw)
    rw [Module.finrank_fin_fun] at h
    omega
  set b := Module.finBasisOfFinrankEq ℂ K hK
  set g : finiteFullRankFrame ℂ 2 3 :=
    ⟨fun i ↦ (b i : Fin 3 → ℂ), b.linearIndependent.map' K.subtype K.ker_subtype⟩
  set f := g.orthonormalize
  have hfK (i : Fin 2) : w ⬝ᵥ f.val i = 0 := by
    have hspan : f.val i ∈ Submodule.span ℂ (range g.val) := by
      rw [← finiteFullRankFrame.span_range_orthonormalize]
      exact Submodule.subset_span (mem_range_self i)
    have hle : Submodule.span ℂ (range g.val) ≤ K := by
      rw [Submodule.span_le]
      rintro _ ⟨j, rfl⟩
      exact (b j).property
    simpa [K] using hle hspan
  refine ⟨f, (Configuration.ofField.eq_or_eq_of_orthogonal (orthogonal_dualPoint f 0)
    (orthogonal_dualPoint f 1) ?_ ?_).resolve_left (mk_val_zero_ne_mk_val_one f)⟩
  · rw [orthogonal_mk, dotProduct_comm]
    exact hfK 0
  · rw [orthogonal_mk, dotProduct_comm]
    exact hfK 1

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

/-- The relation on orthonormal two-frames of `ℂ³` of having the same standard line in `CP²`. -/
@[expose] def lineSetoid : Setoid (finiteOrthonormalFrame ℂ 2 3) :=
  Setoid.ker fun f ↦ range (lineSphereFamily 2 f)

/-- **The moduli space of the standard lines of `CP²`**: the images of the two-spheres
`σ_f : S² → CP²` of the orthonormal two-frames `f` of `ℂ³`, with the quotient topology from the
frames. -/
@[expose] def LineModuli : Type :=
  Quotient lineSetoid

namespace LineModuli

instance : TopologicalSpace LineModuli :=
  inferInstanceAs (TopologicalSpace (Quotient lineSetoid))

instance : CompactSpace LineModuli :=
  inferInstanceAs (CompactSpace (Quotient lineSetoid))

/-- The standard line of an orthonormal two-frame of `ℂ³`. -/
def mk (f : finiteOrthonormalFrame ℂ 2 3) : LineModuli :=
  Quotient.mk lineSetoid f

/-- Every standard line is the line of a frame. -/
theorem mk_surjective : Function.Surjective mk :=
  Quotient.mk_surjective

/-- The standard line of a frame depends continuously on the frame. -/
@[fun_prop]
theorem continuous_mk : Continuous mk :=
  continuous_quotient_mk'

/-- A line of `CP²` is the set of its points. -/
instance : SetLike LineModuli (ComplexProjectiveSpace 2) where
  coe := Quotient.lift (fun f ↦ range (lineSphereFamily 2 f)) fun _ _ h ↦ Setoid.ker_def.1 h
  coe_injective := by
    rintro ⟨f⟩ ⟨g⟩ h
    exact Quotient.sound (Setoid.ker_def.2 h)

/-- The points of the standard line of `f` are the values of its two-sphere `σ_f`. -/
@[simp]
theorem coe_mk (f : finiteOrthonormalFrame ℂ 2 3) :
    (mk f : Set (ComplexProjectiveSpace 2)) = range (lineSphereFamily 2 f) :=
  (rfl)

/-- Two frames have the same standard line exactly when their two-spheres have the same image. -/
theorem mk_eq_mk_iff {f g : finiteOrthonormalFrame ℂ 2 3} :
    mk f = mk g ↔ range (lineSphereFamily 2 f) = range (lineSphereFamily 2 g) := by
  rw [← SetLike.coe_set_eq, coe_mk, coe_mk]

/-- **The line moduli is the dual projective plane**: the homeomorphism from the moduli space of
standard lines of `CP²` to `ℙ ℂ (Fin 3 → ℂ)` sending the line of a frame `f` to `[f₀ × f₁]`. -/
def dualHomeomorph : LineModuli ≃ₜ ℙ ℂ (Fin 3 → ℂ) :=
  have hcont : Continuous (Quotient.lift dualPoint
      fun _ _ h ↦ range_lineSphereFamily_eq_iff.1 (Setoid.ker_def.1 h) :
      LineModuli → ℙ ℂ (Fin 3 → ℂ)) :=
    continuous_quot_lift _ continuous_dualPoint
  hcont.homeoOfEquivCompactToT2 (f := Equiv.ofBijective _ ⟨by
    rintro ⟨f⟩ ⟨g⟩ h
    exact Quotient.sound (Setoid.ker_def.2 (range_lineSphereFamily_eq_iff.2 h)), by
    intro w
    obtain ⟨f, rfl⟩ := dualPoint_surjective w
    exact ⟨mk f, rfl⟩⟩)

/-- The dual point of the standard line of `f` is `[f₀ × f₁]`. -/
@[simp]
theorem dualHomeomorph_mk (f : finiteOrthonormalFrame ℂ 2 3) :
    dualHomeomorph (mk f) = dualPoint f :=
  (rfl)

/-- The standard line with dual point `[f₀ × f₁]` is the standard line of `f`. -/
@[simp]
theorem dualHomeomorph_symm_dualPoint (f : finiteOrthonormalFrame ℂ 2 3) :
    dualHomeomorph.symm (dualPoint f) = mk f :=
  dualHomeomorph.symm_apply_eq.2 (dualHomeomorph_mk f).symm

instance : T2Space LineModuli :=
  dualHomeomorph.isEmbedding.t2Space

/-- **Point-line incidence in `CP²`**: a point `p` lies on a standard line `L` exactly when `p` is
orthogonal to the dual point of `L` for the bilinear dot product. -/
theorem mem_iff (p : ComplexProjectiveSpace 2) (L : LineModuli) :
    p ∈ L ↔ (homeomorphProjectivization 2 p).orthogonal (dualHomeomorph L) := by
  obtain ⟨f, rfl⟩ := mk_surjective L
  rw [← SetLike.mem_coe, coe_mk, dualHomeomorph_mk, mem_range_lineSphereFamily_iff]

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
    rw [mem_ofPred_eq, ← SetLike.mem_coe, ← hg, coe_mk]
    exact mem_range_self x
  · rw [mem_ofPred_eq, ← SetLike.mem_coe, coe_mk] at h
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
