/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Fiber
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
public import TauCeti.Topology.Homotopy.SerreFibration.RelativeCube
public import TauCeti.AlgebraicTopology.Homotopy.Relative.Group

/-!
# The boundary map of a Serre fibration

Let `p : E ⟶ B` be a Serre fibration, `b` a point of `B` and `e` a point of the fibre
`F = p⁻¹(b)`. This file constructs the boundary map

`∂ : π_{n+1}(B, b) → π_n(F, e)`

of the long exact homotopy sequence of `p`, directly by cube lifting.

The group `π_{n+1}(B, b)` is Mathlib's `HomotopyGroup (Option N) B b`, where `n` is the cardinality
of the finite index type `N`; its cube `I^(Option N)` is the cube `I × I^N` with the coordinate
`none` as the distinguished first direction (`TauCeti.piOptionEquivProdHomeomorph`). A
generalized loop `γ` of `B` at `b` is thus a map `I × I^N → B` sending the whole boundary to `b`.
A **cube lift** of `γ` (`TopCat.Hom.IsCubeLift`) is a map `G : I × I^N → E` over `γ` that is
constantly `e` on the face `{1} × I^N` and on the sides `I × ∂I^N`. Its remaining face
`{0} × I^N` lies over `b`, so it is a generalized loop of the fibre at `e`
(`TopCat.Hom.IsCubeLift.face`). This is the convention of relative homotopy groups
(`TauCeti.RelGenLoop`), where the face `{0} × I^N` is the free one: a cube lift is a relative cube
of the pair `(E, F)` lying over `γ`, and its face is the image of that relative cube under the
boundary map of the pair.

Cube lifts exist by the relative cube lifting property of Serre fibrations
(`TauCeti.TopCat.exists_isCubeLift`), and the homotopy class of the face is independent of the
chosen lift and of the representative `γ` of its homotopy class: given lifts `G₀`, `G₁` of
homotopic loops `γ₀`, `γ₁`, a further relative cube lift of the homotopy, prescribed to be `G₀`
and `G₁` on the two ends, restricts on its free face to a homotopy between the faces of `G₀` and
`G₁` (`TopCat.Hom.IsCubeLift.homotopic_face`). This defines the boundary map
`TauCeti.TopCat.fibrationBoundary`, characterized by `∂[γ] = [face of G]` for every cube lift `G`
of `γ` (`TauCeti.TopCat.fibrationBoundary_mk`).

Concatenating two cube lifts along a direction of `I^N` gives a cube lift of the concatenated
loop whose face is the concatenation of the faces (`TopCat.Hom.IsCubeLift.exists_transAt`): as
relative cubes of the pair `(E, F)`, this is `TauCeti.RelGenLoop.boundary_transAt`. Hence
in positive dimensions `∂` is a group homomorphism (`TauCeti.TopCat.fibrationBoundaryHom`), for
Mathlib's group structures `HomotopyGroup.mul_spec`. The boundary map is natural for maps of
fibrations, that is, for commutative squares (`TauCeti.TopCat.fibrationBoundary_map`), and the
two composites `π_{n+1}(E, e) → π_{n+1}(B, b) → π_n(F, e)` and
`π_{n+1}(B, b) → π_n(F, e) → π_n(E, e)` are trivial
(`TauCeti.TopCat.fibrationBoundary_map_hom`, `TauCeti.TopCat.map_fiberι_fibrationBoundary`).

No group structure or exactness is needed for the construction, so `N` may be empty: then `∂`
maps `π_1(B, b)` to the set `π_0(F, e)` of path components of the fibre.

## Main definitions

* `TopCat.Hom.IsCubeLift`: a lift of a generalized loop of the base that is constant on the face
  `{1} × I^N` and on the sides of the cube.
* `TopCat.Hom.IsCubeLift.face`: its free face, a generalized loop of the fibre.
* `TopCat.Hom.IsCubeLift.toRelGenLoop`: a cube lift as a relative cube of the pair `(E, F)`.
* `TauCeti.TopCat.fibrationBoundary`: the boundary map `π_{n+1}(B, b) → π_n(F, e)`.
* `TauCeti.TopCat.fibrationBoundaryHom`: the boundary map as a group homomorphism, in positive
  dimensions.

## Main results

* `TauCeti.TopCat.exists_isCubeLift`: every generalized loop of the base has a cube lift.
* `TopCat.Hom.IsCubeLift.homotopic_face`: lifts of homotopic loops have homotopic faces.
* `TauCeti.TopCat.fibrationBoundary_mk`: `∂[γ]` is the class of the face of any cube lift of
  `γ`.
* `TauCeti.TopCat.fibrationBoundary_mul`: `∂` is multiplicative.
* `TauCeti.TopCat.fibrationBoundary_map`: naturality for maps of fibrations.
* `TauCeti.TopCat.fibrationBoundary_map_hom`, `TauCeti.TopCat.map_fiberι_fibrationBoundary`:
  the composites with the maps induced by `p` and by the fibre inclusion are trivial.

## References

* A. Hatcher, *Algebraic Topology*, Section 4.2, Theorem 4.41 and the long exact sequence of a
  fibration following it.
-/

public noncomputable section

open Set unitInterval CategoryTheory
open scoped Topology Topology.Homotopy

universe u v

namespace TopCat.Hom

variable {E B : TopCat.{u}} (p : E ⟶ B) {b : B} (e : p.fiber b) {N : Type v}

/-- A **cube lift** of a generalized loop `γ` of `B` at `b`, along `p` and at the point `e` of
the fibre over `b`: a map `G : I × I^N → E` lying over `γ`, read on `I × I^N` through
`TauCeti.piOptionEquivProdHomeomorph`, that is constantly `e` on the face `{1} × I^N` and on the
sides `I × ∂I^N`. The remaining face `{0} × I^N` then lies in the fibre
(`TopCat.Hom.IsCubeLift.face`). -/
structure IsCubeLift (γ : Ω^ (Option N) B b) (G : C(I × (I^N), E)) : Prop where
  /-- A cube lift lies over the generalized loop. -/
  map_apply (y : I × (I^N)) :
    p (G y) = γ ((TauCeti.piOptionEquivProdHomeomorph fun _ : Option N ↦ I).symm y)
  /-- A cube lift is constantly `e` on the face `{1} × I^N` and on the sides `I × ∂I^N`. -/
  apply_eq (s : I) (t : I^N) (h : s = 1 ∨ t ∈ Cube.boundary N) : G (s, t) = e.1

variable {p e}

namespace IsCubeLift

variable {γ : Ω^ (Option N) B b} {G : C(I × (I^N), E)}

/-- The face `{0} × I^N` of a cube lift lies in the fibre. -/
theorem apply_zero_mem (hG : p.IsCubeLift e γ G) (t : I^N) : G (0, t) ∈ p ⁻¹' {b} := by
  rw [mem_preimage, mem_singleton_iff, hG.map_apply]
  exact γ.2 _ (TauCeti.piOptionEquivProdHomeomorph_symm_mem_boundary
    (TauCeti.Cube.mk_zero_mem_prodBoundary t))

/-- The free face `{0} × I^N` of a cube lift, a generalized loop of the fibre at `e`. -/
def face (hG : p.IsCubeLift e γ G) : Ω^ N (p.fiber b) e :=
  ⟨⟨fun t ↦ ⟨G (0, t), hG.apply_zero_mem t⟩,
      (G.continuous.comp (Continuous.prodMk_right 0)).subtype_mk _⟩,
    fun t ht ↦ Subtype.ext (hG.apply_eq 0 t (Or.inr ht))⟩

@[simp]
theorem coe_face_apply (hG : p.IsCubeLift e γ G) (t : I^N) : (hG.face t : E) = G (0, t) :=
  (rfl)

/-- A cube lift, as a relative cube (`TauCeti.RelGenLoop`) of the based pair `(E, p⁻¹(b), e)`. -/
def toRelGenLoop (hG : p.IsCubeLift e γ G) :
    TauCeti.RelGenLoop N ⟨TopPair.ofSubset (p ⁻¹' {b}), e⟩ :=
  ⟨G, TauCeti.RelGenLoop.mem_iff.2 ⟨fun t ↦ ⟨⟨_, hG.apply_zero_mem t⟩, rfl⟩, hG.apply_eq⟩⟩

/-- The face of the relative cube of a cube lift is the face of the cube lift. -/
@[simp]
theorem boundary_toRelGenLoop (hG : p.IsCubeLift e γ G) :
    TauCeti.RelGenLoop.boundary hG.toRelGenLoop = hG.face :=
  GenLoop.ext _ _ fun _ ↦ (TauCeti.RelGenLoop.boundary_apply_eq_iff _ _ _).2 rfl

end IsCubeLift

variable (p e) in
/-- The constant map at `e` is a cube lift of the constant generalized loop. -/
theorem isCubeLift_const :
    p.IsCubeLift e (GenLoop.const : Ω^ (Option N) B b) (ContinuousMap.const _ e.1) where
  map_apply _ := p.apply_coe_fiber b e
  apply_eq _ _ _ := rfl

/-- The face of the constant cube lift is the constant generalized loop. -/
@[simp]
theorem face_isCubeLift_const :
    (isCubeLift_const p e (N := N)).face = GenLoop.const :=
  GenLoop.ext _ _ fun _ ↦ rfl

/-- A generalized loop of the total space at `e`, read on `I × I^N`, is a cube lift of its image
under `p`, and its face is constant. -/
theorem isCubeLift_genLoopMap (δ : Ω^ (Option N) E e.1) :
    p.IsCubeLift e (GenLoop.map p.hom (p.apply_coe_fiber b e) δ)
      ((δ : C(I^(Option N), E)).comp
        ((TauCeti.piOptionEquivProdHomeomorph fun _ : Option N ↦ I).symm :
          C(I × (I^N), I^(Option N)))) where
  map_apply _ := by
    rw [ContinuousMap.comp_apply, GenLoop.map_apply]
    rfl
  apply_eq s t h :=
    δ.2 _ (TauCeti.piOptionEquivProdHomeomorph_symm_mem_boundary
      (TauCeti.Cube.mk_mem_prodBoundary h))

/-- The face of the cube lift of the image of a generalized loop of the total space is
constant. -/
@[simp]
theorem face_isCubeLift_genLoopMap (δ : Ω^ (Option N) E e.1) :
    (isCubeLift_genLoopMap (p := p) δ).face = GenLoop.const :=
  GenLoop.ext _ _ fun t ↦ Subtype.ext <|
    δ.2 _ (TauCeti.piOptionEquivProdHomeomorph_symm_mem_boundary
      (TauCeti.Cube.mk_zero_mem_prodBoundary t))

namespace IsCubeLift

variable {E' B' : TopCat.{u}} {p' : E' ⟶ B'} {f : E ⟶ E'} {g : B ⟶ B'}
  {γ : Ω^ (Option N) B b} {G : C(I × (I^N), E)}

/-- A map of fibrations carries cube lifts to cube lifts. -/
theorem comp (hG : p.IsCubeLift e γ G) (sq : CommSq f p p' g) :
    p'.IsCubeLift (sq.fiberMap b e) (GenLoop.map g.hom rfl γ) (f.hom.comp G) where
  map_apply y := by
    rw [ContinuousMap.comp_apply, ← ConcreteCategory.comp_apply, sq.w,
      ConcreteCategory.comp_apply, hG.map_apply, GenLoop.map_apply]
  apply_eq s t h := by
    rw [ContinuousMap.comp_apply, hG.apply_eq s t h, CommSq.fiberMap_apply_coe]

/-- The face of the image of a cube lift under a map of fibrations is the image of its face
under the induced map of fibres. -/
theorem face_comp (hG : p.IsCubeLift e γ G) (sq : CommSq f p p' g) :
    (hG.comp sq).face = GenLoop.map (sq.fiberMap b).hom rfl hG.face :=
  GenLoop.ext _ _ fun t ↦ Subtype.ext <| by
    rw [coe_face_apply, GenLoop.map_apply, ContinuousMap.comp_apply]
    exact (CommSq.fiberMap_apply_coe sq b (hG.face t)).symm

end IsCubeLift

end TopCat.Hom

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B} {b : B} {e : p.fiber b} {N : Type v}

/-- **Cube lifts exist.** Every generalized loop of the base of a Serre fibration has a cube lift
at every point of the fibre. -/
theorem exists_isCubeLift [Finite N] (hp : serreFibrations p) (e : p.fiber b)
    (γ : Ω^ (Option N) B b) : ∃ G, p.IsCubeLift e γ G := by
  set ι := piOptionEquivProdHomeomorph fun _ : Option N ↦ I
  have hbd : ∀ y ∈ Cube.prodBoundary N, γ (ι.symm y) = b :=
    fun y hy ↦ γ.2 _ (piOptionEquivProdHomeomorph_symm_mem_boundary hy)
  obtain ⟨G, hG, hGf⟩ := exists_lift_openBox_of_mem_serreFibrations hp N
    (ContinuousMap.const _ e.1) ⟨fun y ↦ γ (ι.symm (σ y.1, y.2)), by fun_prop⟩ <| by
      rintro ⟨⟨s, t⟩, hst⟩
      refine (p.apply_coe_fiber b e).trans (hbd _ (Cube.mem_prodBoundary_iff.2 ?_)).symm
      rcases mem_cylinderExtensionDomain_iff.1 hst with h | h
      · obtain rfl : s = 0 := h
        exact .inl (.inr symm_zero)
      · exact .inr h
  refine ⟨G.comp ⟨fun y ↦ (σ y.1, y.2), by fun_prop⟩, ⟨fun y ↦ ?_, fun s t h ↦ ?_⟩⟩
  · simpa using congrFun hG (σ y.1, y.2)
  · exact hGf ⟨(σ s, t), mem_cylinderExtensionDomain_iff.2 <|
      h.imp_left fun h ↦ by rw [h, symm_one]⟩

end TauCeti.TopCat

namespace TopCat.Hom.IsCubeLift

variable {E B : TopCat.{u}} {p : E ⟶ B} {b : B} {e : p.fiber b} {N : Type v}

/-- The values prescribed on the bottom and on the sides of the box `I × I^(Option N)` when lifting
a homotopy between two loops with cube lifts `G₀` and `G₁`, with the coordinate `none` as the
homotopy parameter and the time of the lift reversed: `G₀` and `G₁` on the faces where the
parameter is `0` and `1`, and `x₀` elsewhere. -/
private def boxData (G₀ G₁ : C(I × (I^N), E)) (x₀ : E) (x : I × (I^(Option N))) : E :=
  if x.2 none = 0 then G₀ (σ x.1, fun k ↦ x.2 (some k))
  else if x.2 none = 1 then G₁ (σ x.1, fun k ↦ x.2 (some k)) else x₀

variable {γ₀ γ₁ : Ω^ (Option N) B b} {G₀ G₁ : C(I × (I^N), E)}

private theorem boxData_of_eq_zero {x₀ : E} {x : I × (I^(Option N))} (hx : x.2 none = 0) :
    boxData G₀ G₁ x₀ x = G₀ (σ x.1, fun k ↦ x.2 (some k)) :=
  ite_eq_left hx

private theorem boxData_of_eq_one {x₀ : E} {x : I × (I^(Option N))} (hx : x.2 none = 1) :
    boxData G₀ G₁ x₀ x = G₁ (σ x.1, fun k ↦ x.2 (some k)) := by
  rw [boxData, ite_eq_right (by rw [hx]; exact one_ne_zero), ite_eq_left hx]

private theorem boxData_eq (hG₀ : p.IsCubeLift e γ₀ G₀) (hG₁ : p.IsCubeLift e γ₁ G₁)
    {x : I × (I^(Option N))} (hx : x.1 = 0 ∨ (fun k ↦ x.2 (some k)) ∈ Cube.boundary N) :
    boxData G₀ G₁ e.1 x = e.1 := by
  have h : σ x.1 = 1 ∨ (fun k ↦ x.2 (some k)) ∈ Cube.boundary N :=
    hx.imp_left fun h ↦ by rw [h, symm_zero]
  rw [boxData]
  split_ifs
  · exact hG₀.apply_eq _ _ h
  · exact hG₁.apply_eq _ _ h
  · rfl

/-- The prescribed values are continuous on the bottom and the sides of the box, where they agree
with `e`, `G₀` or `G₁` on closed pieces. -/
private theorem continuousOn_boxData [Finite N] (hG₀ : p.IsCubeLift e γ₀ G₀)
    (hG₁ : p.IsCubeLift e γ₁ G₁) :
    ContinuousOn (boxData G₀ G₁ e.1)
      (TauCeti.cylinderExtensionDomain (Cube.boundary (Option N))) := by
  set A := {x : I × (I^(Option N)) | x.1 = 0 ∨ (fun k ↦ x.2 (some k)) ∈ Cube.boundary N}
  set A₀ := {x : I × (I^(Option N)) | x.2 none = 0}
  set A₁ := {x : I × (I^(Option N)) | x.2 none = 1}
  have hD : TauCeti.cylinderExtensionDomain (Cube.boundary (Option N)) ⊆ A ∪ A₀ ∪ A₁ := by
    intro x hx
    rcases TauCeti.mem_cylinderExtensionDomain_iff.1 hx with h | h
    · exact .inl (.inl (.inl h))
    · rcases Cube.boundary_option_iff.1 h with (h | h) | h
      · exact .inl (.inr h)
      · exact .inr h
      · exact .inl (.inl (.inr h))
  have hA : IsClosed A := (isClosed_eq continuous_fst continuous_const).union
    (Cube.isClosed_boundary.preimage (by fun_prop))
  have hA₀ : IsClosed A₀ := isClosed_eq (by fun_prop) continuous_const
  have hA₁ : IsClosed A₁ := isClosed_eq (by fun_prop) continuous_const
  refine ContinuousOn.mono ?_ hD
  exact ((continuousOn_const.congr fun x hx ↦ boxData_eq hG₀ hG₁ hx).union_of_isClosed
    ((G₀.continuous.comp (by fun_prop)).continuousOn.congr fun x hx ↦ boxData_of_eq_zero hx)
      hA hA₀).union_of_isClosed
    ((G₁.continuous.comp (by fun_prop)).continuousOn.congr fun x hx ↦ boxData_of_eq_one hx)
      (hA.union hA₀) hA₁

/-- A homotopy between two loops with cube lifts `G₀` and `G₁` has a relative lift over the box
`I × I^(Option N)` with the prescribed values `boxData` on its bottom and sides. Its top face lies
over `b`. -/
private theorem exists_boxLift [Finite N] (hp : TauCeti.TopCat.serreFibrations p)
    (K : (γ₀ : C(I^(Option N), B)).HomotopyRel γ₁ (Cube.boundary (Option N)))
    (hG₀ : p.IsCubeLift e γ₀ G₀) (hG₁ : p.IsCubeLift e γ₁ G₁) :
    ∃ L : C(I × (I^(Option N)), E), (∀ y, p (L (1, y)) = b) ∧
      ∀ y ∈ Cube.boundary (Option N), L (1, y) = boxData G₀ G₁ e.1 (1, y) := by
  set ι := TauCeti.piOptionEquivProdHomeomorph fun _ : Option N ↦ I
  have hK : ∀ r y, y ∈ TauCeti.Cube.prodBoundary N → K (r, ι.symm y) = b := fun r y hy ↦
    have hy := TauCeti.piOptionEquivProdHomeomorph_symm_mem_boundary hy
    (K.eq_fst r hy).trans (γ₀.2 _ hy)
  let H : C(I × (I^(Option N)), B) :=
    ⟨fun x ↦ K (x.2 none, ι.symm (σ x.1, fun k ↦ x.2 (some k))), by fun_prop⟩
  let f : C(TauCeti.cylinderExtensionDomain (Cube.boundary (Option N)), E) :=
    ⟨fun x ↦ boxData G₀ G₁ e.1 x, (continuousOn_boxData hG₀ hG₁).domRestrict⟩
  have hfx : ∀ x, f x = boxData G₀ G₁ e.1 x := fun _ ↦ rfl
  have hf : ∀ x, p (f x) = H x := by
    rintro ⟨x, hx⟩
    simp only [hfx, H, ContinuousMap.coe_mk]
    rcases TauCeti.mem_cylinderExtensionDomain_iff.1 hx with h | h
    · rw [boxData_eq hG₀ hG₁ (.inl h), p.apply_coe_fiber, hK]
      exact TauCeti.Cube.mem_prodBoundary_iff.2 (.inl (.inr (by rw [h, symm_zero])))
    rcases Cube.boundary_option_iff.1 h with (h | h) | h
    · rw [boxData_of_eq_zero h, hG₀.map_apply, h, K.apply_zero]
      rfl
    · rw [boxData_of_eq_one h, hG₁.map_apply, h, K.apply_one]
      rfl
    · rw [boxData_eq hG₀ hG₁ (.inr h), p.apply_coe_fiber, hK]
      exact TauCeti.Cube.mem_prodBoundary_iff.2 (.inr h)
  obtain ⟨L, hL, hLf⟩ :=
    TauCeti.TopCat.exists_lift_openBox_of_mem_serreFibrations hp (Option N) f H hf
  refine ⟨L, fun y ↦ ?_, fun y hy ↦
    hLf ⟨(1, y), TauCeti.mem_cylinderExtensionDomain_iff.2 (.inr hy)⟩⟩
  rw [← Function.comp_apply (f := p), hL]
  simp only [H, ContinuousMap.coe_mk, symm_one]
  exact hK _ _ (TauCeti.Cube.mk_zero_mem_prodBoundary _)

/-- **Lifts of homotopic loops have homotopic faces.** If `γ₀` and `γ₁` are homotopic
generalized loops of the base of a Serre fibration, the faces of any cube lifts `G₀` of `γ₀` and
`G₁` of `γ₁` at the same point of the fibre are homotopic generalized loops of the fibre. -/
theorem homotopic_face [Finite N] (hp : TauCeti.TopCat.serreFibrations p)
    (hG₀ : p.IsCubeLift e γ₀ G₀) (hG₁ : p.IsCubeLift e γ₁ G₁) (h : GenLoop.Homotopic γ₀ γ₁) :
    GenLoop.Homotopic hG₀.face hG₁.face := by
  obtain ⟨K⟩ := h
  obtain ⟨L, hL₁, hLg⟩ := exists_boxLift hp K hG₀ hG₁
  set ι := TauCeti.piOptionEquivProdHomeomorph fun _ : Option N ↦ I
  have hLι : ∀ r t, (r = 0 ∨ r = 1) ∨ t ∈ Cube.boundary N →
      L (1, ι.symm (r, t)) = boxData G₀ G₁ e.1 (1, ι.symm (r, t)) := fun r t h ↦
    hLg _ (TauCeti.piOptionEquivProdHomeomorph_symm_mem_boundary
      (TauCeti.Cube.mem_prodBoundary_iff.2 h))
  refine ⟨{ toFun := fun x ↦ ⟨L (1, ι.symm x), hL₁ _⟩
            continuous_toFun := (L.continuous.comp (by fun_prop)).subtype_mk _
            map_zero_left := fun t ↦ Subtype.ext ?_
            map_one_left := fun t ↦ Subtype.ext ?_
            prop' := fun r t ht ↦ Subtype.ext ?_ }⟩
  · simp only [GenLoop.coe_coe]
    rw [hLι 0 t (.inl (.inl rfl)), boxData_of_eq_zero (by simp [ι])]
    simpa [ι] using (coe_face_apply hG₀ t).symm
  · simp only [GenLoop.coe_coe]
    rw [hLι 1 t (.inl (.inr rfl)), boxData_of_eq_one (by simp [ι])]
    simpa [ι] using (coe_face_apply hG₁ t).symm
  · simp only [ContinuousMap.coe_mk, GenLoop.coe_coe]
    rw [hLι r t (.inr ht), boxData_eq hG₀ hG₁ (.inr (by simpa [ι] using ht))]
    exact ((coe_face_apply hG₀ t).trans (hG₀.apply_eq 0 t (.inr ht))).symm

/-- **Concatenation of cube lifts.** Two cube lifts of `γ₁` and `γ₂`, run one after the other in
the `j`-th direction of `I^N`, form a cube lift of the concatenation of `γ₁` and `γ₂` in that
direction, whose face is the concatenation of the faces. -/
theorem exists_transAt [DecidableEq N] (j : N) {γ₁ γ₂ : Ω^ (Option N) B b}
    {G₁ G₂ : C(I × (I^N), E)} (hG₁ : p.IsCubeLift e γ₁ G₁) (hG₂ : p.IsCubeLift e γ₂ G₂) :
    ∃ (G : C(I × (I^N), E)) (hG : p.IsCubeLift e (GenLoop.transAt (some j) γ₁ γ₂) G),
      hG.face = GenLoop.transAt j hG₁.face hG₂.face := by
  -- The concatenation is that of the relative cubes of the two lifts.
  set Q := TauCeti.RelGenLoop.transAt j hG₁.toRelGenLoop hG₂.toRelGenLoop
  -- The ambient space of the pair is `E` only after unfolding `TopPair.ofSubset`, so `p` cannot be
  -- rewritten along values of `Q`; name its underlying map as a map to `E` instead.
  obtain ⟨G, hGQ⟩ : ∃ G : C(I × (I^N), E), G = Q.1 := ⟨_, rfl⟩
  have hQ : ∀ s t, G (s, t) = if (t j : ℝ) ≤ 1 / 2
      then G₁ (s, Function.update t j <| Set.projIcc 0 1 zero_le_one (2 * t j))
      else G₂ (s, Function.update t j <| Set.projIcc 0 1 zero_le_one (2 * t j - 1)) := by
    subst hGQ
    exact TauCeti.RelGenLoop.transAt_apply j _ _
  have hG : p.IsCubeLift e (GenLoop.transAt (some j) γ₁ γ₂) G := by
    refine ⟨fun ⟨s, t⟩ ↦ ?_, fun s t h ↦ by
      subst hGQ
      exact (TauCeti.RelGenLoop.mem_iff.1 Q.2).2 s t h⟩
    rw [hQ, GenLoop.transAt, GenLoop.coe_copy]
    simp only [TauCeti.piOptionEquivProdHomeomorph_symm_apply_some]
    split_ifs
    · rw [hG₁.map_apply, TauCeti.piOptionEquivProdHomeomorph_symm_update]
    · rw [hG₂.map_apply, TauCeti.piOptionEquivProdHomeomorph_symm_update]
  refine ⟨G, hG, ?_⟩
  rw [← boundary_toRelGenLoop hG, ← boundary_toRelGenLoop hG₁, ← boundary_toRelGenLoop hG₂]
  subst hGQ
  exact TauCeti.RelGenLoop.boundary_transAt j _ _

end TopCat.Hom.IsCubeLift

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B} {b : B} {N : Type v} [Finite N]

/-- **The boundary map of a Serre fibration** `∂ : π_{n+1}(B, b) → π_n(F, e)`, for the fibre
`F = p⁻¹(b)` and a point `e` of it: the class of a generalized loop `γ` of `B` at `b` goes to the
class of the face of a cube lift of `γ` at `e` (`TauCeti.TopCat.fibrationBoundary_mk`). -/
def fibrationBoundary (hp : serreFibrations p) (e : p.fiber b) :
    HomotopyGroup (Option N) B b → HomotopyGroup N (p.fiber b) e :=
  Quotient.lift (fun γ ↦ ⟦(exists_isCubeLift hp e γ).choose_spec.face⟧) fun _ _ h ↦
    Quotient.sound <| (exists_isCubeLift hp e _).choose_spec.homotopic_face hp
      (exists_isCubeLift hp e _).choose_spec h

/-- The boundary map sends the class of a generalized loop to the class of the face of any of
its cube lifts. -/
theorem fibrationBoundary_mk (hp : serreFibrations p) {e : p.fiber b} {γ : Ω^ (Option N) B b}
    {G : C(I × (I^N), E)} (hG : p.IsCubeLift e γ G) :
    fibrationBoundary hp e ⟦γ⟧ = ⟦hG.face⟧ :=
  Quotient.sound <| (exists_isCubeLift hp e γ).choose_spec.homotopic_face hp hG
    (GenLoop.Homotopic.refl γ)

/-- The boundary map sends the class of the constant loop to the class of the constant loop. -/
@[simp]
theorem fibrationBoundary_mk_const (hp : serreFibrations p) (e : p.fiber b) :
    fibrationBoundary hp e ⟦(GenLoop.const : Ω^ (Option N) B b)⟧ = ⟦GenLoop.const⟧ := by
  rw [fibrationBoundary_mk hp (p.isCubeLift_const e), _root_.TopCat.Hom.face_isCubeLift_const]

/-- The composite `π_{n+1}(E, e) → π_{n+1}(B, b) → π_n(F, e)` of the map induced by `p` and the
boundary map is trivial. -/
@[simp]
theorem fibrationBoundary_map_hom (hp : serreFibrations p) (e : p.fiber b)
    (a : HomotopyGroup (Option N) E e.1) :
    fibrationBoundary hp e (HomotopyGroup.map p.hom (p.apply_coe_fiber b e) a) =
      ⟦GenLoop.const⟧ := by
  induction a using Quotient.inductionOn with
  | h δ =>
    rw [HomotopyGroup.map_mk,
      fibrationBoundary_mk hp (_root_.TopCat.Hom.isCubeLift_genLoopMap δ),
      _root_.TopCat.Hom.face_isCubeLift_genLoopMap]

/-- The composite `π_{n+1}(B, b) → π_n(F, e) → π_n(E, e)` of the boundary map and the map induced
by the inclusion of the fibre is trivial. -/
@[simp]
theorem map_fiberι_fibrationBoundary (hp : serreFibrations p) (e : p.fiber b)
    (a : HomotopyGroup (Option N) B b) :
    HomotopyGroup.map (p.fiberι b).hom (p.fiberι_apply b e) (fibrationBoundary hp e a) =
      ⟦GenLoop.const⟧ := by
  induction a using Quotient.inductionOn with
  | h γ =>
    obtain ⟨G, hG⟩ := exists_isCubeLift hp e γ
    -- The fibre inclusion is the embedding of the pair `(E, p⁻¹(b))` of `hG.toRelGenLoop`.
    set R := hG.toRelGenLoop
    have hι : GenLoop.map (p.fiberι b).hom (p.fiberι_apply b e) (RelGenLoop.boundary R) =
        GenLoop.map (TopPair.ofSubset (p ⁻¹' {b})).map.hom rfl (RelGenLoop.boundary R) :=
      GenLoop.ext _ _ fun t ↦ (GenLoop.map_apply _ _ _ t).trans
        ((p.fiberι_apply b _).trans
          (GenLoop.map_apply (TopPair.ofSubset (p ⁻¹' {b})).map.hom rfl _ t).symm)
    rw [fibrationBoundary_mk hp hG, HomotopyGroup.map_mk, ← hG.boundary_toRelGenLoop, hι]
    exact Quotient.sound (RelGenLoop.homotopic_map_boundary_const R)

/-- **Naturality of the boundary map** for a map of Serre fibrations, that is, a commutative
square from `p` to `p'`. -/
theorem fibrationBoundary_map {E' B' : TopCat.{u}} {p' : E' ⟶ B'} {f : E ⟶ E'} {g : B ⟶ B'}
    (hp : serreFibrations p) (hp' : serreFibrations p') (sq : CommSq f p p' g) (e : p.fiber b)
    (a : HomotopyGroup (Option N) B b) :
    fibrationBoundary hp' (sq.fiberMap b e) (HomotopyGroup.map g.hom rfl a) =
      HomotopyGroup.map (sq.fiberMap b).hom rfl (fibrationBoundary hp e a) := by
  induction a using Quotient.inductionOn with
  | h γ =>
    obtain ⟨G, hG⟩ := exists_isCubeLift hp e γ
    rw [HomotopyGroup.map_mk, fibrationBoundary_mk hp' (hG.comp sq), fibrationBoundary_mk hp hG,
      HomotopyGroup.map_mk, hG.face_comp sq]

/-- **The boundary map is multiplicative** in positive dimensions. -/
theorem fibrationBoundary_mul [DecidableEq N] [Nonempty N] (hp : serreFibrations p)
    (e : p.fiber b) (a₁ a₂ : HomotopyGroup (Option N) B b) :
    fibrationBoundary hp e (a₁ * a₂) = fibrationBoundary hp e a₁ * fibrationBoundary hp e a₂ := by
  obtain ⟨j⟩ := ‹Nonempty N›
  induction a₁ using Quotient.inductionOn with | h γ₁ => ?_
  induction a₂ using Quotient.inductionOn with | h γ₂ => ?_
  obtain ⟨G₁, hG₁⟩ := exists_isCubeLift hp e γ₁
  obtain ⟨G₂, hG₂⟩ := exists_isCubeLift hp e γ₂
  obtain ⟨G, hG, hface⟩ := hG₂.exists_transAt j hG₁
  rw [fibrationBoundary_mk hp hG₁, fibrationBoundary_mk hp hG₂]
  simp only [HomotopyGroup.mul_spec (i := some j), HomotopyGroup.mul_spec (i := j)]
  rw [fibrationBoundary_mk hp hG, hface]

/-- The boundary map sends the identity to the identity. -/
@[simp]
theorem fibrationBoundary_one [DecidableEq N] [Nonempty N] (hp : serreFibrations p)
    (e : p.fiber b) : fibrationBoundary hp e (1 : HomotopyGroup (Option N) B b) = 1 := by
  rw [_root_.HomotopyGroup.one_def, fibrationBoundary_mk_const, ← _root_.HomotopyGroup.one_def]

/-- **The boundary map of a Serre fibration** `π_{n+1}(B, b) →* π_n(F, e)` as a group
homomorphism, in positive dimensions. -/
def fibrationBoundaryHom [DecidableEq N] [Nonempty N] (hp : serreFibrations p) (e : p.fiber b) :
    HomotopyGroup (Option N) B b →* HomotopyGroup N (p.fiber b) e where
  toFun := fibrationBoundary hp e
  map_one' := fibrationBoundary_one hp e
  map_mul' := fibrationBoundary_mul hp e

@[simp]
theorem fibrationBoundaryHom_apply [DecidableEq N] [Nonempty N] (hp : serreFibrations p)
    (e : p.fiber b) (a : HomotopyGroup (Option N) B b) :
    fibrationBoundaryHom hp e a = fibrationBoundary hp e a :=
  (rfl)

end TauCeti.TopCat
