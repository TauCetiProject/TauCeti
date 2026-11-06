/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Category.TopCat.Fiber
public import TauCeti.Topology.ContinuousMap.GlueHalves
public import TauCeti.Topology.Homotopy.Cube.Basic
public import TauCeti.Topology.Homotopy.GenLoop.Homotopic
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
public import TauCeti.Topology.Homotopy.SerreFibration.RelativeCube

/-!
# The exact homotopy sequence of a Serre fibration

Let `p : E → B` be a Serre fibration (`TauCeti.TopCat.serreFibrations`), `b : B` a point and
`e` a point of the fibre `F = p⁻¹(b)` (`TopCat.Hom.fiber`). This file constructs the boundary map
`∂ : π_{n+1}(B, b) → π_n(F, e)` and proves that the sequence of pointed sets

`π_{n+1}(E, e) → π_{n+1}(B, b) → π_n(F, e) → π_n(E, e) → π_n(B, b)`

is exact at its three middle terms, where the maps other than `∂` are induced by the inclusion
`F ↪ E` and by `p`. Here `n` is the cardinality of an arbitrary finite index type `N`; the group
`π_{n+1}(B, b)` is modelled on the cube `I^(Option N)`, whose coordinate `none` is the
distinguished direction. Since `N` may be empty, the three statements cover every term of the
long exact sequence

`⋯ → π_{n+1}(B) → π_n(F) → π_n(E) → π_n(B) → ⋯ → π_1(B) → π_0(F) → π_0(E) → π_0(B)`,

with exactness of pointed sets at the low end, where `π_0` is the set of path components.

## The boundary map

Read a generalized loop `γ : I^(Option N) → B` at `b` as a map `I × I^N → B`, a homotopy of maps
`I^N → B`. A *boundary lift* of `γ` (`TauCeti.TopCat.IsBoundaryLift`) is a lift `G : I × I^N → E`
of it along `p` that is constant at `e` on the face `{0} × I^N` and over the boundary of `I^N`.
Such lifts exist by relative homotopy lifting for cubes
(`TauCeti.TopCat.exists_lift_openBox_of_mem_serreFibrations`), and the end `G(1, ·)` of a boundary
lift is a generalized loop in the fibre (`TauCeti.TopCat.IsBoundaryLift.endLoop`). The class of
this end loop does not depend on the lift nor on the representative of the class of `γ`: two
boundary lifts of homotopic loops are compared by one further relative lift over the cube
`I × I^(Option N)` (`TauCeti.TopCat.IsBoundaryLift.homotopic_endLoop`). This defines
`TauCeti.TopCat.fibrationBoundary`, characterized by `TauCeti.TopCat.fibrationBoundary_mk` for
every boundary lift.

The boundary map is natural for maps of Serre fibrations, that is, for commutative squares
(`TauCeti.TopCat.fibrationBoundary_map`). For `n ≥ 1` it is a group homomorphism
(`TauCeti.TopCat.fibrationBoundary_mul`, bundled as `TauCeti.TopCat.fibrationBoundaryHom`):
concatenating two boundary lifts along a direction of `I^N` gives a boundary lift of the
concatenated loops, in the order of Mathlib's `HomotopyGroup.mul_spec`.

## Exactness

* At `π_n(F, e)`: a boundary lift is a null-homotopy in `E` of its end loop; conversely a
  null-homotopy in `E` of a loop in the fibre is a boundary lift of its projection
  (`TauCeti.TopCat.mem_range_fibrationBoundary_iff`).
* At `π_n(E, e)`: a null-homotopy in `B` of the projection of a loop in `E` lifts, relative to the
  boundary, to a homotopy in `E` from that loop to a loop in the fibre
  (`TauCeti.TopCat.mem_range_homotopyGroupMap_fiberι_iff`).
* At `π_{n+1}(B, b)`: a cube in `E` is a boundary lift of its projection, with constant end; and
  if the end of a boundary lift is null-homotopic in the fibre, then the lift followed by that
  null-homotopy is a cube in `E` whose projection is homotopic to the original cube
  (`TauCeti.TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq`).

When the total space has trivial homotopy groups, as for a path fibration, exactness makes the
boundary map surjective with trivial kernel
(`TauCeti.TopCat.surjective_fibrationBoundary_of_subsingleton`,
`TauCeti.TopCat.fibrationBoundary_eq_const_iff_of_subsingleton`).

## References

* A. Hatcher, *Algebraic Topology*, Theorem 4.41 and its proof.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter IV.8.
-/

public section

noncomputable section

open CategoryTheory Set unitInterval
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B} {b : B} {e : p.fiber b} {N : Type*}

/-! ### Generalized loops in the fibre -/

-- Not `simp`: `GenLoop.map_apply` rewrites the left-hand side first, and the result is closed by
-- `TopCat.Hom.fiberι_apply`. Use it as an explicit rewrite.
/-- A generalized loop in the fibre, pushed into `E` along the fibre inclusion, takes the values
of the loop. -/
theorem _root_.GenLoop.map_fiberι_apply {x : E} (hx : p.fiberι b e = x)
    (β : Ω^ N (p.fiber b) e) (t : I^N) : GenLoop.map (p.fiberι b).hom hx β t = (β t).1 :=
  (GenLoop.map_apply _ _ β t).trans (TopCat.Hom.fiberι_apply p b _)

/-! ### Boundary lifts -/

variable (p e) in
/-- A **boundary lift** of a generalized loop `γ : I^(Option N) → B` at `b`, read as a map
`I × I^N → B`, is a lift `G : I × I^N → E` of it along `p` which is constant at `e` on the face
`{0} × I^N` and over the boundary of `I^N`. Its end `G(1, ·)` lies in the fibre over `b`
(`TauCeti.TopCat.IsBoundaryLift.endLoop`). -/
structure IsBoundaryLift (γ : Ω^ (Option N) B b) (G : C(I × I^N, E)) : Prop where
  /-- The lift lies over the loop `γ`. -/
  proj_apply (y : I × I^N) : p (G y) = γ ((piOptionEquivProdHomeomorph fun _ => I).symm y)
  /-- The lift starts at `e`. -/
  apply_zero (t : I^N) : G (0, t) = e.1
  /-- The lift is stationary at `e` over the boundary of `I^N`. -/
  apply_of_mem_boundary (s : I) {t : I^N} (ht : t ∈ Cube.boundary N) : G (s, t) = e.1

namespace IsBoundaryLift

variable {γ : Ω^ (Option N) B b} {G : C(I × I^N, E)}

/-- The end of a boundary lift lies in the fibre over `b`. -/
theorem proj_apply_one (hG : IsBoundaryLift p e γ G) (t : I^N) : p (G (1, t)) = b :=
  (hG.proj_apply _).trans
    (GenLoop.apply_symm_of_mem_prodBoundary γ (Cube.mk_mem_prodBoundary (.inl rfl)))

/-- The end `G(1, ·)` of a boundary lift, a generalized loop at `e` in the fibre of `p` over
`b`. -/
def endLoop (hG : IsBoundaryLift p e γ G) : Ω^ N (p.fiber b) e :=
  ⟨⟨fun t => ⟨G (1, t), hG.proj_apply_one t⟩, by fun_prop⟩, fun _ ht =>
    Subtype.ext (hG.apply_of_mem_boundary 1 ht)⟩

@[simp]
theorem endLoop_apply_coe (hG : IsBoundaryLift p e γ G) (t : I^N) :
    (hG.endLoop t).1 = G (1, t) :=
  (rfl)

/-- The end loop of a boundary lift is null-homotopic in `E`. -/
theorem homotopic_map_endLoop_const (hG : IsBoundaryLift p e γ G) :
    GenLoop.Homotopic (GenLoop.map (p.fiberι b).hom (TopCat.Hom.fiberι_apply p b e) hG.endLoop)
      GenLoop.const :=
  GenLoop.homotopic_of_continuousMap (G.comp ⟨fun y => (σ y.1, y.2), by fun_prop⟩)
    (fun t => by rw [GenLoop.map_fiberι_apply, endLoop_apply_coe]; simp)
    (fun t => by simp [hG.apply_zero])
    fun s t ht => by simp [hG.apply_of_mem_boundary _ ht]

end IsBoundaryLift

/-- Every generalized loop of the base of a Serre fibration has a boundary lift. -/
theorem exists_isBoundaryLift (hp : serreFibrations p) [Finite N] (e : p.fiber b)
    (γ : Ω^ (Option N) B b) : ∃ G, IsBoundaryLift p e γ G := by
  obtain ⟨G, hG, hGf⟩ := exists_lift_openBox_of_mem_serreFibrations hp N
    (ContinuousMap.const _ e.1)
    ((γ : C(I^(Option N), B)).comp
      ((piOptionEquivProdHomeomorph fun _ : Option N => I).symm : C(I × I^N, I^(Option N))))
    fun y => by
      rw [ContinuousMap.comp_apply, ContinuousMap.coe_ofClass]
      refine e.2.trans (GenLoop.apply_symm_of_mem_prodBoundary γ ?_).symm
      rcases mem_cylinderExtensionDomain_iff.1 y.2 with h | h
      · exact Cube.mem_prodBoundary_iff.2 (Or.inl (Or.inl h))
      · exact Cube.mem_prodBoundary_iff.2 (Or.inr h)
  exact ⟨G, ⟨fun y => congrFun hG y, fun t => hGf ⟨(0, t), zero_mem_cylinderExtensionDomain t⟩,
    fun s t ht => hGf ⟨(s, t), mem_cylinderExtensionDomain_iff.2 (Or.inr ht)⟩⟩⟩

/-- **Independence of the boundary lift.** Boundary lifts of homotopic generalized loops have
homotopic end loops in the fibre. -/
theorem IsBoundaryLift.homotopic_endLoop (hp : serreFibrations p) [Finite N]
    {γ γ' : Ω^ (Option N) B b} (h : GenLoop.Homotopic γ γ') {G G' : C(I × I^N, E)}
    (hG : IsBoundaryLift p e γ G) (hG' : IsBoundaryLift p e γ' G') :
    GenLoop.Homotopic hG.endLoop hG'.endLoop := by
  obtain ⟨K⟩ := h
  let φ := piOptionEquivProdHomeomorph fun _ : Option N => I
  -- A point `(s, y)` of `I × I^(Option N)` has lifting parameter `s`, homotopy parameter
  -- `y none` and the point `y ∘ some` of `I^N`.
  let q : (I × I^(Option N)) → (I × I^N) := fun x => (x.1, fun i => x.2 (some i))
  let H : C(I × I^(Option N), B) := ⟨fun x => K (x.2 none, φ.symm (q x)), by fun_prop⟩
  -- On the bottom face and over the boundary of `I^(Option N)`, either the homotopy parameter is
  -- `0` or `1`, or `K` is evaluated on the boundary of the cube, where it is stationary.
  have hK {x : I × I^(Option N)} (hx : x ∈ cylinderExtensionDomain (Cube.boundary (Option N))) :
      (x.2 none = 0 ∨ x.2 none = 1) ∨ φ.symm (q x) ∈ Cube.boundary (Option N) := by
    rcases mem_cylinderExtensionDomain_iff.1 hx with hx | hx
    · exact .inr (piOptionEquivProdHomeomorph_symm_mem_boundary
        (Cube.mem_prodBoundary_iff.2 (.inl (.inl hx))))
    · rcases Cube.boundary_option_iff.1 hx with hx | hx
      · exact .inl hx
      · exact .inr (piOptionEquivProdHomeomorph_symm_mem_boundary
          (Cube.mem_prodBoundary_iff.2 (.inr hx)))
  -- The prescribed lift: `G` for homotopy parameter at most `1/2` and `G'` above. On the
  -- prescribed set both are `e` where the homotopy parameter is `1/2`.
  let q' : C(cylinderExtensionDomain (Cube.boundary (Option N)), I × I^N) :=
    ⟨fun x => q x.1, by fun_prop⟩
  let f : C(cylinderExtensionDomain (Cube.boundary (Option N)), E) :=
    ContinuousMap.glueHalves ⟨fun x => x.1.2 none, by fun_prop⟩ (G.comp q') (G'.comp q')
      fun x hx => by
        simp only [ContinuousMap.coe_mk] at hx
        simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk, q', q]
        rcases mem_cylinderExtensionDomain_iff.1 x.2 with h0 | hb
        · rw [h0, hG.apply_zero, hG'.apply_zero]
        · rcases Cube.boundary_option_iff.1 hb with hu | ht
          · rcases hu with hu | hu <;> norm_num [hu] at hx
          · rw [hG.apply_of_mem_boundary _ ht, hG'.apply_of_mem_boundary _ ht]
  have hf (x : cylinderExtensionDomain (Cube.boundary (Option N))) : p (f x) = H x := by
    by_cases hu : (x.1.2 none : ℝ) ≤ 2⁻¹
    · rw [ContinuousMap.glueHalves_of_le _ _ _ _ hu, ContinuousMap.comp_apply, hG.proj_apply]
      simp only [H, q', ContinuousMap.coe_mk]
      rcases hK x.2 with (h0 | h1) | hz
      · rw [h0, K.apply_zero, GenLoop.coe_coe]
      · norm_num [h1] at hu
      · exact (K.eq_fst _ hz).symm
    · rw [ContinuousMap.glueHalves_of_not_le _ _ _ _ hu, ContinuousMap.comp_apply,
        hG'.proj_apply]
      simp only [H, q', ContinuousMap.coe_mk]
      rcases hK x.2 with (h0 | h1) | hz
      · norm_num [h0] at hu
      · rw [h1, K.apply_one, GenLoop.coe_coe]
      · exact (K.eq_snd _ hz).symm
  obtain ⟨L, hL, hLf⟩ := exists_lift_openBox_of_mem_serreFibrations hp (Option N) f H hf
  -- The prescribed set contains the points over the ends of the homotopy and over `∂I^N`.
  have hmem {u : I} {t : I^N} (h : (u = 0 ∨ u = 1) ∨ t ∈ Cube.boundary N) :
      ((1 : I), φ.symm (u, t)) ∈ cylinderExtensionDomain (Cube.boundary (Option N)) :=
    mem_cylinderExtensionDomain_iff.2 (.inr (Cube.boundary_option_iff.2 (by simpa [φ] using h)))
  have hLf' {u : I} {t : I^N} (h : (u = 0 ∨ u = 1) ∨ t ∈ Cube.boundary N) :
      L (1, φ.symm (u, t)) = if (u : ℝ) ≤ 2⁻¹ then G (1, t) else G' (1, t) := by
    rw [hLf ⟨_, hmem h⟩]
    split_ifs with hu <;> simp [f, q', q, φ, hu]
  have hLb (u : I) (t : I^N) : p (L (1, φ.symm (u, t))) = b := by
    rw [← Function.comp_apply (f := p), hL]
    exact (K.eq_fst _ (piOptionEquivProdHomeomorph_symm_mem_boundary
      (Cube.mem_prodBoundary_iff.2 (.inl (.inr rfl))))).trans
        (GenLoop.apply_symm_of_mem_prodBoundary γ (Cube.mem_prodBoundary_iff.2 (.inl (.inr rfl))))
  refine GenLoop.homotopic_of_continuousMap
    ⟨fun y => ⟨L (1, φ.symm y), hLb y.1 y.2⟩, by fun_prop⟩ (fun t => ?_) (fun t => ?_)
    fun u t ht => ?_ <;> apply Subtype.ext <;> dsimp only [ContinuousMap.coe_mk]
  · rw [hLf' (.inl (.inl rfl)), hG.endLoop_apply_coe]
    simp
  · rw [hLf' (.inl (.inr rfl)), hG'.endLoop_apply_coe]
    norm_num
  · rw [hLf' (.inr ht)]
    split_ifs
    · exact hG.apply_of_mem_boundary _ ht
    · exact hG'.apply_of_mem_boundary _ ht

/-! ### The boundary map -/

/-- The **boundary map** `∂ : π_{n+1}(B, b) → π_n(F, e)` of a Serre fibration `p`, where `F` is
the fibre of `p` over `b` and `n` is the cardinality of `N`: the class of a generalized loop `γ`
goes to the class of the end loop of any boundary lift of `γ`
(`TauCeti.TopCat.fibrationBoundary_mk`). -/
def fibrationBoundary (hp : serreFibrations p) [Finite N] (e : p.fiber b) :
    HomotopyGroup (Option N) B b → HomotopyGroup N (p.fiber b) e :=
  Quotient.lift (fun γ => ⟦(exists_isBoundaryLift hp e γ).choose_spec.endLoop⟧) fun _ _ h =>
    Quotient.sound (IsBoundaryLift.homotopic_endLoop hp h _ _)

/-- The boundary of the class of `γ` is the class of the end loop of any boundary lift of `γ`. -/
theorem fibrationBoundary_mk (hp : serreFibrations p) [Finite N] {γ : Ω^ (Option N) B b}
    {G : C(I × I^N, E)} (hG : IsBoundaryLift p e γ G) :
    fibrationBoundary hp e ⟦γ⟧ = ⟦hG.endLoop⟧ :=
  Quotient.sound (IsBoundaryLift.homotopic_endLoop hp (GenLoop.Homotopic.refl γ) _ hG)

/-- The boundary map sends the class of the constant loop to the class of the constant loop. -/
@[simp]
theorem fibrationBoundary_const (hp : serreFibrations p) [Finite N] :
    fibrationBoundary hp e (⟦GenLoop.const⟧ : HomotopyGroup (Option N) B b) = ⟦GenLoop.const⟧ := by
  have hG : IsBoundaryLift p e GenLoop.const (ContinuousMap.const (I × I^N) e.1) :=
    { proj_apply _ := e.2
      apply_zero _ := rfl
      apply_of_mem_boundary _ _ _ := rfl }
  rw [fibrationBoundary_mk hp hG]
  exact congrArg _ (GenLoop.ext _ _ fun t => Subtype.ext (hG.endLoop_apply_coe t))

/-- **Naturality of the boundary map.** A map of Serre fibrations, that is, a commutative square
from `p` to `p'`, intertwines their boundary maps with the induced maps on the bases and on the
fibres. -/
theorem fibrationBoundary_map {E' B' : TopCat.{u}} {p' : E' ⟶ B'} {f : E ⟶ E'} {g : B ⟶ B'}
    (sq : CommSq f p p' g) (hp : serreFibrations p) (hp' : serreFibrations p') [Finite N]
    (a : HomotopyGroup (Option N) B b) :
    fibrationBoundary hp' (sq.fiberMap b e) (HomotopyGroup.map g.hom rfl a) =
      HomotopyGroup.map (sq.fiberMap b).hom rfl (fibrationBoundary hp e a) := by
  induction a using Quotient.inductionOn with | h γ => ?_
  obtain ⟨G, hG⟩ := exists_isBoundaryLift hp e γ
  have hfG : IsBoundaryLift p' (sq.fiberMap b e) (GenLoop.map g.hom rfl γ) (f.hom.comp G) :=
    { proj_apply y := by
        rw [ContinuousMap.comp_apply, ← ConcreteCategory.comp_apply, sq.w,
          ConcreteCategory.comp_apply, hG.proj_apply, GenLoop.map_apply]
      apply_zero t := by
        rw [ContinuousMap.comp_apply, hG.apply_zero, CommSq.fiberMap_apply_coe]
      apply_of_mem_boundary s t ht := by
        rw [ContinuousMap.comp_apply, hG.apply_of_mem_boundary _ ht, CommSq.fiberMap_apply_coe] }
  rw [HomotopyGroup.map_mk, fibrationBoundary_mk hp' hfG, fibrationBoundary_mk hp hG,
    HomotopyGroup.map_mk]
  congr 1
  refine GenLoop.ext _ _ fun t => Subtype.ext ?_
  rw [hfG.endLoop_apply_coe, ContinuousMap.comp_apply, GenLoop.map_apply]
  exact (CommSq.fiberMap_apply_coe sq b (hG.endLoop t)).symm

/-! ### The boundary map is a homomorphism -/

section Group

variable [DecidableEq N]

/-- **The boundary map is multiplicative.** For `n ≥ 1`, the boundary of a product in
`π_{n+1}(B, b)` is the product of the boundaries in `π_n(F, e)`. -/
theorem fibrationBoundary_mul (hp : serreFibrations p) [Finite N] [Nonempty N]
    (a a' : HomotopyGroup (Option N) B b) :
    fibrationBoundary hp e (a * a') = fibrationBoundary hp e a * fibrationBoundary hp e a' := by
  induction a using Quotient.inductionOn with | h γ => ?_
  induction a' using Quotient.inductionOn with | h γ' => ?_
  obtain ⟨G, hG⟩ := exists_isBoundaryLift hp e γ
  obtain ⟨G', hG'⟩ := exists_isBoundaryLift hp e γ'
  let j := Classical.arbitrary N
  -- The lifts concatenated along the direction `j`, in the order of `HomotopyGroup.mul_spec`.
  let Gc : C(I × I^N, E) := ContinuousMap.glueHalves ⟨fun y => y.2 j, by fun_prop⟩
    (G'.comp ⟨fun y => (y.1, Function.update y.2 j (projIcc 0 1 zero_le_one (2 * y.2 j))),
      by fun_prop⟩)
    (G.comp ⟨fun y => (y.1, Function.update y.2 j (projIcc 0 1 zero_le_one (2 * y.2 j - 1))),
      by fun_prop⟩)
    fun y hy => by
      simp only [ContinuousMap.coe_mk] at hy
      simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
      rw [hG'.apply_of_mem_boundary _ ⟨j, by norm_num [hy]⟩,
        hG.apply_of_mem_boundary _ ⟨j, by norm_num [hy]⟩]
  have hGc_apply (y : I × I^N) : Gc y = if (y.2 j : ℝ) ≤ 1 / 2
      then G' (y.1, Function.update y.2 j (projIcc 0 1 zero_le_one (2 * y.2 j)))
      else G (y.1, Function.update y.2 j (projIcc 0 1 zero_le_one (2 * y.2 j - 1))) := by
    rw [one_div]
    split_ifs with hj <;> simp [Gc, hj]
  have hGc : IsBoundaryLift p e (GenLoop.transAt (some j) γ' γ) Gc :=
    { proj_apply := fun ⟨s, t⟩ => by
        simp only [hGc_apply, GenLoop.transAt, GenLoop.coe_copy,
          piOptionEquivProdHomeomorph_symm_apply_some, update_piOptionEquivProdHomeomorph_symm_some]
        split_ifs
        · exact hG'.proj_apply _
        · exact hG.proj_apply _
      apply_zero t := by
        rw [hGc_apply]
        split_ifs
        · exact hG'.apply_zero _
        · exact hG.apply_zero _
      apply_of_mem_boundary s t ht := by
        rw [hGc_apply]
        split_ifs with hj
        · refine hG'.apply_of_mem_boundary _ (Cube.update_mem_boundary ht ?_)
          rintro (h0 | h1)
          · exact .inl (projIcc_eq_zero.2 (by simp [h0]))
          · norm_num [h1] at hj
        · refine hG.apply_of_mem_boundary _ (Cube.update_mem_boundary ht ?_)
          rintro (h0 | h1)
          · norm_num [h0] at hj
          · exact .inr (projIcc_eq_one.2 (by norm_num [h1])) }
  have hend : hGc.endLoop = GenLoop.transAt j hG'.endLoop hG.endLoop := by
    refine GenLoop.ext _ _ fun t => Subtype.ext ?_
    rw [hGc.endLoop_apply_coe]
    simp only [hGc_apply, GenLoop.transAt, GenLoop.coe_copy]
    split_ifs
    exacts [(hG'.endLoop_apply_coe _).symm, (hG.endLoop_apply_coe _).symm]
  rw [fibrationBoundary_mk hp hG, fibrationBoundary_mk hp hG']
  simp only [HomotopyGroup.mul_spec (i := some j), HomotopyGroup.mul_spec (i := j)]
  rw [fibrationBoundary_mk hp hGc, hend]

/-- For `n ≥ 1`, the boundary map `π_{n+1}(B, b) → π_n(F, e)` of a Serre fibration as a group
homomorphism. -/
def fibrationBoundaryHom (hp : serreFibrations p) [Finite N] [Nonempty N] (e : p.fiber b) :
    HomotopyGroup (Option N) B b →* HomotopyGroup N (p.fiber b) e :=
  MonoidHom.mk' (fibrationBoundary hp e) (fibrationBoundary_mul hp)

@[simp]
theorem coe_fibrationBoundaryHom (hp : serreFibrations p) [Finite N] [Nonempty N]
    (e : p.fiber b) : ⇑(fibrationBoundaryHom hp e (N := N)) = fibrationBoundary hp e :=
  (rfl)

end Group

/-! ### Exactness -/

/-- **Exactness at `π_n(F, e)`.** A class of the fibre is a boundary exactly when it becomes
trivial in `π_n(E, e)`. -/
theorem mem_range_fibrationBoundary_iff (hp : serreFibrations p) [Finite N]
    {a : HomotopyGroup N (p.fiber b) e} :
    a ∈ range (fibrationBoundary hp e) ↔
      HomotopyGroup.map (p.fiberι b).hom (TopCat.Hom.fiberι_apply p b e) a =
        (⟦GenLoop.const⟧ : HomotopyGroup N E e.1) := by
  constructor
  · rintro ⟨c, rfl⟩
    induction c using Quotient.inductionOn with | h γ => ?_
    obtain ⟨G, hG⟩ := exists_isBoundaryLift hp e γ
    rw [fibrationBoundary_mk hp hG, HomotopyGroup.map_mk]
    exact Quotient.sound hG.homotopic_map_endLoop_const
  · intro h
    induction a using Quotient.inductionOn with | h β => ?_
    rw [HomotopyGroup.map_mk] at h
    obtain ⟨K⟩ := Quotient.exact h
    -- The null-homotopy of `β` in `E`, run backwards, is a boundary lift of its projection.
    let G : C(I × I^N, E) := ⟨fun y => K (σ y.1, y.2), by fun_prop⟩
    have hG0 (t : I^N) : G (0, t) = e.1 := by simp [G]
    have hG1 (t : I^N) : G (1, t) = (β t).1 := by
      simp only [G, ContinuousMap.coe_mk, symm_one, K.apply_zero]
      exact GenLoop.map_fiberι_apply _ β t
    have hGb (s : I) {t : I^N} (ht : t ∈ Cube.boundary N) : G (s, t) = e.1 := by
      simp only [G, ContinuousMap.coe_mk, K.eq_fst _ ht]
      exact (GenLoop.map_fiberι_apply _ β t).trans (congrArg Subtype.val (GenLoop.boundary β t ht))
    have hpG : ∀ y ∈ Cube.prodBoundary N, p.hom.comp G y = b := by
      rintro ⟨s, t⟩ hy
      rw [ContinuousMap.comp_apply]
      rcases Cube.mem_prodBoundary_iff.1 hy with (rfl | rfl) | ht
      · rw [hG0]; exact e.2
      · rw [hG1]; exact (β t).2
      · rw [hGb s ht]; exact e.2
    have hG : IsBoundaryLift p e (GenLoop.ofProd _ hpG) G :=
      { proj_apply y := by simp [GenLoop.ofProd_apply]
        apply_zero := hG0
        apply_of_mem_boundary := hGb }
    refine ⟨⟦GenLoop.ofProd _ hpG⟧, ?_⟩
    rw [fibrationBoundary_mk hp hG]
    congr 1
    exact GenLoop.ext _ _ fun t => Subtype.ext (hG1 t)

/-- **Exactness at `π_n(E, e)`.** A class of the total space comes from the fibre exactly when it
becomes trivial in `π_n(B, b)`. -/
theorem mem_range_homotopyGroupMap_fiberι_iff (hp : serreFibrations p) [Finite N]
    {a : HomotopyGroup N E e.1} :
    a ∈ range (HomotopyGroup.map (p.fiberι b).hom (TopCat.Hom.fiberι_apply p b e)) ↔
      HomotopyGroup.map p.hom (Set.mem_singleton_iff.1 e.2) a =
        (⟦GenLoop.const⟧ : HomotopyGroup N B b) := by
  constructor
  · rintro ⟨c, rfl⟩
    induction c using Quotient.inductionOn with | h β => ?_
    rw [HomotopyGroup.map_mk, HomotopyGroup.map_mk]
    congr 1
    refine GenLoop.ext _ _ fun t => ?_
    rw [GenLoop.map_apply, GenLoop.map_fiberι_apply, GenLoop.const_apply]
    exact (β t).2
  · intro h
    induction a using Quotient.inductionOn with | h α => ?_
    rw [HomotopyGroup.map_mk] at h
    obtain ⟨K⟩ := Quotient.exact h
    -- Lift the null-homotopy of `p ∘ α`, starting at `α` and stationary over `∂I^N`.
    obtain ⟨L, hL, hLf⟩ := exists_lift_openBox_of_mem_serreFibrations hp N
      ((α : C(I^N, E)).comp ⟨fun y => y.1.2, by fun_prop⟩) K.toContinuousMap fun y => by
        obtain ⟨⟨s, t⟩, hy⟩ := y
        rcases mem_cylinderExtensionDomain_iff.1 hy with (rfl : s = 0) | ht
        · simp
        · simp [K.eq_fst _ ht]
    have hL0 (t : I^N) : L (0, t) = α t := hLf ⟨(0, t), zero_mem_cylinderExtensionDomain t⟩
    have hLb (s : I) {t : I^N} (ht : t ∈ Cube.boundary N) : L (s, t) = e.1 :=
      (hLf ⟨(s, t), mem_cylinderExtensionDomain_iff.2 (.inr ht)⟩).trans (GenLoop.boundary α t ht)
    have hL1 (t : I^N) : p (L (1, t)) = b := by
      rw [← Function.comp_apply (f := p), hL]
      exact (K.apply_one t).trans GenLoop.const_apply
    let β : Ω^ N (p.fiber b) e :=
      ⟨⟨fun t => ⟨L (1, t), hL1 t⟩, by fun_prop⟩, fun t ht => Subtype.ext (hLb 1 ht)⟩
    refine ⟨⟦β⟧, (Quotient.sound ?_).symm⟩
    exact GenLoop.homotopic_of_continuousMap L hL0
      (fun t => (GenLoop.map_fiberι_apply _ β t).symm)
      fun s t ht => hLb s ht

/-- **Exactness at `π_{n+1}(B, b)`.** A class of the base comes from the total space exactly when
its boundary is trivial. -/
theorem mem_range_homotopyGroupMap_iff_fibrationBoundary_eq (hp : serreFibrations p) [Finite N]
    {a : HomotopyGroup (Option N) B b} :
    a ∈ range (HomotopyGroup.map p.hom (Set.mem_singleton_iff.1 e.2)) ↔
      fibrationBoundary hp e a = (⟦GenLoop.const⟧ : HomotopyGroup N (p.fiber b) e) := by
  let φ := piOptionEquivProdHomeomorph fun _ : Option N => I
  constructor
  · rintro ⟨c, rfl⟩
    induction c using Quotient.inductionOn with | h δ => ?_
    -- A cube in `E` is a boundary lift of its projection, with constant end loop.
    have hG : IsBoundaryLift p e (GenLoop.map p.hom (Set.mem_singleton_iff.1 e.2) δ)
        ((δ : C(I^(Option N), E)).comp (φ.symm : C(I × I^N, I^(Option N)))) :=
      { proj_apply y := by simp [φ]
        apply_zero t := GenLoop.apply_symm_of_mem_prodBoundary δ (Cube.mk_zero_mem_prodBoundary t)
        apply_of_mem_boundary s t ht :=
          GenLoop.apply_symm_of_mem_prodBoundary δ (Cube.mem_prodBoundary_iff.2 (.inr ht)) }
    rw [HomotopyGroup.map_mk, fibrationBoundary_mk hp hG]
    congr 1
    exact GenLoop.ext _ _ fun t => Subtype.ext
      (GenLoop.apply_symm_of_mem_prodBoundary δ (Cube.mk_mem_prodBoundary (.inl rfl)))
  · intro h
    induction a using Quotient.inductionOn with | h γ => ?_
    obtain ⟨G, hG⟩ := exists_isBoundaryLift hp e γ
    rw [fibrationBoundary_mk hp hG] at h
    obtain ⟨K⟩ := Quotient.exact h
    -- Follow the boundary lift `G` by the null-homotopy `K` of its end loop in the fibre: this is a
    -- generalized loop in `E` whose projection is `γ` run at double speed and then stopped.
    let D : C(I × I^N, E) := ContinuousMap.glueHalves ContinuousMap.fst
      (G.comp ⟨fun y => (projIcc 0 1 zero_le_one (2 * y.1), y.2), by fun_prop⟩)
      (⟨fun y => (K (projIcc 0 1 zero_le_one (2 * y.1 - 1), y.2)).1, by fun_prop⟩)
      fun y hy => by
        simp only [ContinuousMap.fst_apply] at hy
        simp only [ContinuousMap.comp_apply, ContinuousMap.coe_mk]
        norm_num [hy, K.apply_zero]
    have hD_apply (y : I × I^N) : D y = if (y.1 : ℝ) ≤ 1 / 2
        then G (projIcc 0 1 zero_le_one (2 * y.1), y.2)
        else (K (projIcc 0 1 zero_le_one (2 * y.1 - 1), y.2)).1 := by
      rw [one_div]
      split_ifs with hy <;> simp [D, hy]
    have hD : ∀ y ∈ Cube.prodBoundary N, D y = e.1 := by
      rintro ⟨s, t⟩ hy
      rw [hD_apply]
      rcases Cube.mem_prodBoundary_iff.1 hy with (rfl | rfl) | ht
      · norm_num [hG.apply_zero]
      · norm_num [K.apply_one]
      · split_ifs
        · exact hG.apply_of_mem_boundary _ ht
        · rw [K.eq_fst _ ht]
          exact congrArg Subtype.val (GenLoop.boundary hG.endLoop t ht)
    refine ⟨⟦GenLoop.ofProd D hD⟧, Quotient.sound <| GenLoop.homotopic_of_continuousMap
      ⟨fun x => γ (φ.symm (projIcc 0 1 zero_le_one ((2 - x.1) * x.2 none),
        fun i => x.2 (some i))), by fun_prop⟩ (fun z => ?_) (fun z => ?_) fun u z hz => ?_⟩
    · -- At the start, the homotopy is the projection of the concatenated loop.
      simp only [ContinuousMap.coe_mk, Icc.coe_zero, sub_zero, GenLoop.map_apply,
        GenLoop.ofProd_apply, piOptionEquivProdHomeomorph_apply, hD_apply]
      split_ifs with hz
      · exact (hG.proj_apply _).symm
      · rw [projIcc_eq_one.2 (by linarith)]
        exact (GenLoop.apply_symm_of_mem_prodBoundary γ
          (Cube.mk_mem_prodBoundary (.inl rfl))).trans (K _).2.symm
    · -- At the end, the homotopy is `γ`.
      simp only [ContinuousMap.coe_mk, Icc.coe_one]
      rw [show (2 - 1) * (z none : ℝ) = z none by ring, projIcc_val,
        ← piOptionEquivProdHomeomorph_apply, Homeomorph.symm_apply_apply]
    · -- Over the boundary of `I^(Option N)`, the homotopy is stationary at `b`.
      simp only [ContinuousMap.coe_mk]
      refine GenLoop.apply_symm_of_mem_prodBoundary γ (Cube.mem_prodBoundary_iff.2 ?_)
      rcases Cube.boundary_option_iff.1 hz with (h0 | h1) | ht
      · exact .inl (.inl (projIcc_eq_zero.2 (by simp [h0])))
      · exact .inl (.inr (projIcc_eq_one.2 (by simp only [h1, Icc.coe_one]; linarith [u.2.2])))
      · exact .inr ht

/-! ### Fibrations with a weakly contractible total space -/

/-- If the homotopy group `π_{n+1}(E, e)` of the total space of a Serre fibration is trivial, then
a class of `π_{n+1}(B, b)` has trivial boundary only if it is trivial itself. -/
theorem fibrationBoundary_eq_const_iff_of_subsingleton (hp : serreFibrations p) [Finite N]
    [Subsingleton (HomotopyGroup (Option N) E e.1)] {a : HomotopyGroup (Option N) B b} :
    fibrationBoundary hp e a = ⟦GenLoop.const⟧ ↔ a = ⟦GenLoop.const⟧ := by
  rw [← mem_range_homotopyGroupMap_iff_fibrationBoundary_eq hp]
  refine ⟨fun ⟨c, hc⟩ ↦ ?_, fun h ↦ ⟨⟦GenLoop.const⟧, ?_⟩⟩
  · rw [← hc, Subsingleton.elim c ⟦GenLoop.const⟧, HomotopyGroup.map_mk, GenLoop.map_const]
  · rw [h, HomotopyGroup.map_mk, GenLoop.map_const]

/-- If the homotopy group `π_n(E, e)` of the total space of a Serre fibration is trivial, then the
boundary map `π_{n+1}(B, b) → π_n(F, e)` is surjective. -/
theorem surjective_fibrationBoundary_of_subsingleton (hp : serreFibrations p) [Finite N]
    [Subsingleton (HomotopyGroup N E e.1)] :
    Function.Surjective (fibrationBoundary hp e (N := N)) := fun _ ↦
  (mem_range_fibrationBoundary_iff hp).2 (Subsingleton.elim _ _)

end TauCeti.TopCat
