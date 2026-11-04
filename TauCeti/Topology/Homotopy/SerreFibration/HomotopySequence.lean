/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Topology.Homotopy.Cube.Basic
public import TauCeti.Topology.Homotopy.HomotopyGroup.Map
public import TauCeti.Topology.Homotopy.HomotopyGroup.TransAt
public import TauCeti.Topology.Homotopy.SerreFibration.RelativeCube

/-!
# The homotopy sequence of a Serre fibration

Let `p : E ⟶ B` be a Serre fibration, `e₀ : E` a point and `F = p⁻¹(p e₀)` the fibre through it,
based at `e₀`. This file constructs the boundary map

`∂ : π_{n+1}(B, p e₀) → π_n(F, e₀)`

(`TauCeti.TopCat.fibrationBoundary`) directly by lifting cubes, and proves that the sequence of
pointed sets

`π_{n+1}(E, e₀) → π_{n+1}(B, p e₀) → π_n(F, e₀) → π_n(E, e₀) → π_n(B, p e₀)`

is exact at its three middle terms, for every finite index type `N` of cardinality `n`. Here the
outer maps are induced by `p` and by the inclusion `F ↪ E`, and exactness of `f`, `g` means that
the elements sent by `g` to the class of the constant map are exactly the image of `f`. In
positive dimensions `∂` is moreover a group homomorphism
(`TauCeti.TopCat.fibrationBoundaryHom`).

A class of `π_{n+1}(B, p e₀) = π_{Option N}(B, p e₀)` is represented by a cube
`γ : I^(Option N) → B` sending the boundary to `p e₀`; read it as a homotopy `I × I^N → B` in
the coordinate `none`. A **boundary lift** of `γ` (`TauCeti.TopCat.IsBoundaryLift`) is a lift
`G : I × I^N → E` of this homotopy which is constant at `e₀` on the bottom face `{0} × I^N`
and on the sides `I × ∂I^N`. Boundary lifts exist by the relative cube lifting property of
Serre fibrations (`TauCeti.TopCat.exists_lift_openBox_of_mem_serreFibrations`), and the top
face `y ↦ G (1, y)` of a boundary lift lies in `F` and is constant at `e₀` on `∂I^N`, so it is
a generalized loop in `F` (`TauCeti.TopCat.IsBoundaryLift.topFace`). Its class is `∂ [γ]`.
That it does not depend on the lift or on the representative is proved by one further relative
lift, of a homotopy between two representatives, with the two given lifts prescribed on its
ends (`TauCeti.TopCat.IsBoundaryLift.homotopic_topFace`).

The three exactness statements are the standard cube manipulations:

* at `π_n(E, e₀)`: a null-homotopy in `B` of `p ∘ δ` lifts, starting at `δ` and fixed on `∂I^N`,
  to a homotopy in `E` from `δ` to a cube in `F`;
* at `π_n(F, e₀)`: a boundary lift is a null-homotopy in `E` of its top face, and conversely a
  null-homotopy in `E` of a cube in `F` is a boundary lift of its own projection;
* at `π_{n+1}(B, p e₀)`: if the top face of a boundary lift `G` of `γ` is null-homotopic in `F`,
  stacking the null-homotopy on top of `G` gives a cube in `E` whose projection is `γ`
  concatenated with a constant cube.

The index type `N` may be empty, so these statements include the low end
`π₁(B) → π₀(F) → π₀(E) → π₀(B)` of the sequence, as pointed sets.

## Main definitions

* `TauCeti.TopCat.IsBoundaryLift`: boundary lifts of a cube in the base.
* `TauCeti.TopCat.IsBoundaryLift.topFace`: the top face of a boundary lift, a cube in the fibre.
* `TauCeti.TopCat.fibrationBoundary`: the boundary map `π_{n+1}(B, p e₀) → π_n(F, e₀)`.
* `TauCeti.TopCat.fibrationBoundaryHom`: the boundary map as a group homomorphism.

## Main results

* `TauCeti.TopCat.IsBoundaryLift.fibrationBoundary_mk`: `∂ [γ]` is the class of the top face of
  any boundary lift of `γ`.
* `TauCeti.TopCat.mem_range_homotopyGroupMap_subtypeVal_iff`: exactness at `π_n(E, e₀)`.
* `TauCeti.TopCat.mem_range_fibrationBoundary_iff`: exactness at `π_n(F, e₀)`.
* `TauCeti.TopCat.mem_range_homotopyGroupMap_iff_fibrationBoundary_eq`: exactness at
  `π_{n+1}(B, p e₀)`.
* `TauCeti.TopCat.fibrationBoundary_mul`: `∂` is multiplicative.

## References

* A. Hatcher, *Algebraic Topology*, Cambridge University Press, 2002, Theorem 4.41.
* G. W. Whitehead, *Elements of Homotopy Theory*, GTM 61, Springer, 1978, Chapter IV.8.
-/

public section

noncomputable section

open CategoryTheory Set unitInterval
open scoped Topology Topology.Homotopy

universe u

namespace TauCeti.TopCat

variable {E B : TopCat.{u}} {p : E ⟶ B} {e₀ : E} {N : Type*}

/-! ### Clamped affine reparametrizations of the unit interval -/

/-- The clamp of a real number in `[0, 1]` to `I` is that number. -/
private theorem coe_projIcc_of_mem {r : ℝ} (h₀ : 0 ≤ r) (h₁ : r ≤ 1) :
    (projIcc (0 : ℝ) 1 zero_le_one r : ℝ) = r := by
  rw [projIcc_of_mem _ ⟨h₀, h₁⟩]

/-! ### Boundary lifts -/

/-- A cube `G : I × I^N → E` is a **boundary lift** of `γ ∈ Ω^(Option N) B (p e₀)` when it lies
over `γ`, with the first coordinate of `G` corresponding to the coordinate `none` of `γ`, and it
is constant at `e₀` on its bottom face `{0} × I^N` and on its sides `I × ∂I^N`. Its top face
then lies in the fibre `p⁻¹(p e₀)` (`TauCeti.TopCat.IsBoundaryLift.topFace`). -/
structure IsBoundaryLift (p : E ⟶ B) (e₀ : E) (γ : Ω^ (Option N) B (p e₀))
    (G : C(I × (I^N), E)) : Prop where
  /-- The cube lies over `γ`. -/
  proj_apply (x : I × (I^N)) : p (G x) = γ ((piOptionEquivProdHomeomorph fun _ => I).symm x)
  /-- The cube is constant at `e₀` on its bottom face and on its sides. -/
  apply_eq (x : I × (I^N)) : x ∈ cylinderExtensionDomain (Cube.boundary N) → G x = e₀

/-- A point of the bottom face or of the sides of `I × I^N` lies on the boundary of the cube
`I^(Option N)`. -/
private theorem symm_mem_boundary_of_mem {x : I × (I^N)}
    (hx : x ∈ cylinderExtensionDomain (Cube.boundary N)) :
    (piOptionEquivProdHomeomorph fun _ : Option N => I).symm x ∈ Cube.boundary (Option N) :=
  piOptionEquivProdHomeomorph_symm_mem_boundary <| Cube.mem_prodBoundary_iff.2
    ((mem_cylinderExtensionDomain_iff.1 hx).elim (fun h => Or.inl (Or.inl h)) Or.inr)

namespace IsBoundaryLift

variable {γ : Ω^ (Option N) B (p e₀)} {G : C(I × (I^N), E)}

/-- The top face of a boundary lift lies over the basepoint. -/
theorem proj_apply_one (h : IsBoundaryLift p e₀ γ G) (y : I^N) : p (G (1, y)) = p e₀ := by
  rw [h.proj_apply]
  exact γ.2 _ (piOptionEquivProdHomeomorph_symm_mem_boundary (Cube.mk_mem_prodBoundary (.inl rfl)))

/-- The top face `y ↦ G (1, y)` of a boundary lift `G`, as a generalized loop in the fibre
`p⁻¹(p e₀)` based at `e₀`. -/
def topFace (h : IsBoundaryLift p e₀ γ G) : Ω^ N (p ⁻¹' {p e₀}) ⟨e₀, rfl⟩ :=
  ⟨⟨fun y => ⟨G (1, y), h.proj_apply_one y⟩, by fun_prop⟩, fun y hy =>
    Subtype.ext (h.apply_eq _ (mem_cylinderExtensionDomain_of_mem hy))⟩

/-- A boundary lift is constant at `e₀` on its bottom face. -/
theorem apply_zero (h : IsBoundaryLift p e₀ γ G) (y : I^N) : G (0, y) = e₀ :=
  h.apply_eq _ (zero_mem_cylinderExtensionDomain y)

/-- A boundary lift is constant at `e₀` on its sides. -/
theorem apply_of_mem (h : IsBoundaryLift p e₀ γ G) (t : I) {y : I^N} (hy : y ∈ Cube.boundary N) :
    G (t, y) = e₀ :=
  h.apply_eq _ (mem_cylinderExtensionDomain_of_mem hy)

/-- The top face of a boundary lift `G` takes the values `y ↦ G (1, y)`. -/
@[simp]
theorem coe_topFace_apply (h : IsBoundaryLift p e₀ γ G) (y : I^N) :
    (h.topFace y : E) = G (1, y) :=
  (rfl)

end IsBoundaryLift

/-- **Boundary lifts exist**: every cube in the base of a Serre fibration has a boundary lift. -/
theorem exists_isBoundaryLift [Finite N] (hp : serreFibrations p) (γ : Ω^ (Option N) B (p e₀)) :
    ∃ G, IsBoundaryLift p e₀ γ G := by
  obtain ⟨G, hG, hGe⟩ := exists_lift_openBox_of_mem_serreFibrations hp N
    (ContinuousMap.const _ e₀)
    ((γ : C(I^(Option N), B)).comp
      ((piOptionEquivProdHomeomorph fun _ : Option N => I).symm : C(I × (I^N), I^(Option N))))
    fun x => by simpa using (γ.2 _ (symm_mem_boundary_of_mem x.2)).symm
  exact ⟨G, fun x => congrFun hG x, fun x hx => hGe ⟨x, hx⟩⟩

/-- **Independence of the top face.** Boundary lifts of homotopic cubes in the base have
homotopic top faces in the fibre. -/
theorem IsBoundaryLift.homotopic_topFace [Finite N] (hp : serreFibrations p)
    {γ₀ γ₁ : Ω^ (Option N) B (p e₀)} (hγ : GenLoop.Homotopic γ₀ γ₁) {G₀ G₁ : C(I × (I^N), E)}
    (h₀ : IsBoundaryLift p e₀ γ₀ G₀) (h₁ : IsBoundaryLift p e₀ γ₁ G₁) :
    GenLoop.Homotopic h₀.topFace h₁.topFace := by
  obtain ⟨Φ⟩ := hγ
  let e := piOptionEquivProdHomeomorph fun _ : Option N => I
  -- The homotopy `Φ` is lifted on the cube `I × I^(Option N)`. Its first coordinate `t` is the
  -- direction `none` of `γ₀` and `γ₁`, its coordinate `none` is the homotopy parameter `s`, and
  -- its coordinates `some i` are those of `I^N`.
  let H : C(I × (I^(Option N)), B) :=
    ⟨fun x => Φ (x.2 none, e.symm (x.1, fun i => x.2 (some i))), by fun_prop⟩
  -- The prescribed lift on the bottom face and the sides: `G₀` for `s ≤ 1 / 2` and `G₁` for
  -- `s ≥ 1 / 2`, both squeezed onto their bottom faces, where they are `e₀`, at `s = 1 / 2`.
  let g : C(I × (I^(Option N)), E) :=
    ⟨fun x => if (x.2 none : ℝ) ≤ 1 / 2
      then G₀ (projIcc 0 1 zero_le_one (x.1 * (1 - 2 * (x.2 none : ℝ))), fun i => x.2 (some i))
      else G₁ (projIcc 0 1 zero_le_one (x.1 * (2 * (x.2 none : ℝ) - 1)), fun i => x.2 (some i)),
      by
      refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const
        fun x hx => ?_
      rw [projIcc_eq_zero.2 (by rw [hx]; norm_num), projIcc_eq_zero.2 (by rw [hx]; norm_num),
        h₀.apply_zero, h₁.apply_zero]⟩
  have g_apply (t s : I) (y : I^N) : g (t, e.symm (s, y)) = if (s : ℝ) ≤ 1 / 2
      then G₀ (projIcc 0 1 zero_le_one (t * (1 - 2 * (s : ℝ))), y)
      else G₁ (projIcc 0 1 zero_le_one (t * (2 * (s : ℝ) - 1)), y) := by
    simp [g, e]
  have H_apply (t s : I) (y : I^N) : H (t, e.symm (s, y)) = Φ (s, e.symm (t, y)) := by
    simp [H, e]
  -- `g` takes the prescribed values on the bottom face and the sides.
  have g_zero (z : I^(Option N)) : g (0, z) = e₀ := by
    obtain ⟨⟨s, y⟩, rfl⟩ := e.symm.surjective z
    rw [g_apply]
    split_ifs
    · rw [projIcc_eq_zero.2 (by simp), h₀.apply_zero]
    · rw [projIcc_eq_zero.2 (by simp), h₁.apply_zero]
  have g_of_mem (t s : I) {y : I^N} (hy : y ∈ Cube.boundary N) : g (t, e.symm (s, y)) = e₀ := by
    rw [g_apply]
    split_ifs
    · exact h₀.apply_eq _ (mem_cylinderExtensionDomain_of_mem hy)
    · exact h₁.apply_eq _ (mem_cylinderExtensionDomain_of_mem hy)
  have g_zero_left (t : I) (y : I^N) : g (t, e.symm (0, y)) = G₀ (t, y) := by
    norm_num [g_apply, projIcc_val]
  have g_one_left (t : I) (y : I^N) : g (t, e.symm (1, y)) = G₁ (t, y) := by
    norm_num [g_apply, projIcc_val]
  -- `γ₀` takes the basepoint value on the boundary.
  have Φ_of_mem (s : I) {x : I × (I^N)} (hx : x ∈ Cube.prodBoundary N) :
      Φ (s, e.symm x) = p e₀ :=
    (Φ.eq_fst s (piOptionEquivProdHomeomorph_symm_mem_boundary hx)).trans
      (γ₀.2 _ (piOptionEquivProdHomeomorph_symm_mem_boundary hx))
  have hgH (x : I × (I^(Option N))) (hx : x ∈ cylinderExtensionDomain (Cube.boundary (Option N))) :
      p (g x) = H x := by
    obtain ⟨t, z⟩ := x
    obtain ⟨⟨s, y⟩, rfl⟩ := e.symm.surjective z
    rw [H_apply]
    rcases mem_cylinderExtensionDomain_iff.1 hx with (rfl : t = 0) | hz
    · rw [g_zero, Φ_of_mem s (Cube.mk_zero_mem_prodBoundary y)]
    · rw [← piOptionEquivProdHomeomorph_mem_prodBoundary_iff, Homeomorph.apply_symm_apply,
        Cube.mem_prodBoundary_iff] at hz
      rcases hz with ((rfl : s = 0) | (rfl : s = 1)) | hy
      · rw [g_zero_left, h₀.proj_apply, Φ.apply_zero, GenLoop.coe_coe]
      · rw [g_one_left, h₁.proj_apply, Φ.apply_one, GenLoop.coe_coe]
      · rw [g_of_mem t s hy, Φ_of_mem s (Cube.mk_mem_prodBoundary (.inr hy))]
  obtain ⟨L, hL, hLg⟩ := exists_lift_openBox_of_mem_serreFibrations hp (Option N)
    (g.restrict _) H fun x => hgH x.1 x.2
  have hL' (x : I × (I^(Option N))) : p (L x) = H x := congrFun hL x
  have hLg' (t : I) {z : I^(Option N)} (hz : z ∈ Cube.boundary (Option N)) : L (t, z) = g (t, z) :=
    hLg ⟨(t, z), mem_cylinderExtensionDomain_of_mem hz⟩
  have hsymm (s : I) {y : I^N} (h : s = 0 ∨ s = 1 ∨ y ∈ Cube.boundary N) :
      e.symm (s, y) ∈ Cube.boundary (Option N) := by
    rcases h with rfl | h
    · exact piOptionEquivProdHomeomorph_symm_mem_boundary (Cube.mk_zero_mem_prodBoundary y)
    · exact piOptionEquivProdHomeomorph_symm_mem_boundary (Cube.mk_mem_prodBoundary h)
  -- The top face of `L` is the required homotopy in the fibre.
  have hLF (x : I × (I^N)) : p (L (1, e.symm x)) = p e₀ := by
    obtain ⟨s, y⟩ := x
    rw [hL', H_apply]
    exact Φ_of_mem s (Cube.mk_mem_prodBoundary (.inl rfl))
  refine ⟨{ toFun := fun x => ⟨L (1, e.symm x), hLF x⟩
            continuous_toFun := (L.continuous.comp
              (continuous_const.prodMk e.symm.continuous)).subtype_mk _
            map_zero_left := fun y => Subtype.ext ?_
            map_one_left := fun y => Subtype.ext ?_
            prop' := fun s y hy => Subtype.ext ?_ }⟩
  · dsimp only
    rw [hLg' 1 (hsymm 0 (.inl rfl)), g_zero_left]
    exact (h₀.coe_topFace_apply y).symm
  · dsimp only
    rw [hLg' 1 (hsymm 1 (.inr (.inl rfl))), g_one_left]
    exact (h₁.coe_topFace_apply y).symm
  · exact (hLg' 1 (hsymm s (.inr (.inr hy)))).trans ((g_of_mem 1 s hy).trans
      ((h₀.apply_of_mem 1 hy).symm.trans (h₀.coe_topFace_apply y).symm))

/-! ### The boundary map -/

/-- The **boundary map** `∂ : π_{n+1}(B, p e₀) → π_n(F, e₀)` of a Serre fibration `p` into the
homotopy groups of its fibre `F = p⁻¹(p e₀)`: the class of a cube `γ` in the base goes to the
class of the top face of a boundary lift of `γ`, which does not depend on the choice of the lift
(`TauCeti.TopCat.IsBoundaryLift.fibrationBoundary_mk`). -/
def fibrationBoundary [Finite N] (hp : serreFibrations p) (e₀ : E) :
    HomotopyGroup (Option N) B (p e₀) → HomotopyGroup N (p ⁻¹' {p e₀}) ⟨e₀, rfl⟩ :=
  Quotient.lift (fun γ => ⟦(exists_isBoundaryLift hp γ).choose_spec.topFace⟧) fun _ _ h =>
    Quotient.sound (IsBoundaryLift.homotopic_topFace hp h _ _)

/-- **The boundary of a class is the class of the top face of any boundary lift.** -/
theorem IsBoundaryLift.fibrationBoundary_mk [Finite N] (hp : serreFibrations p)
    {γ : Ω^ (Option N) B (p e₀)} {G : C(I × (I^N), E)} (h : IsBoundaryLift p e₀ γ G) :
    fibrationBoundary hp e₀ ⟦γ⟧ = ⟦h.topFace⟧ :=
  Quotient.sound (homotopic_topFace hp (GenLoop.Homotopic.refl γ) _ h)

/-- The boundary map sends the class of the constant cube to the class of the constant cube. -/
@[simp]
theorem fibrationBoundary_const [Finite N] (hp : serreFibrations p) :
    fibrationBoundary hp e₀ ⟦(GenLoop.const : Ω^ (Option N) B (p e₀))⟧ = ⟦GenLoop.const⟧ := by
  have h : IsBoundaryLift p e₀ (GenLoop.const : Ω^ (Option N) B (p e₀))
      (ContinuousMap.const _ e₀) := ⟨fun _ => rfl, fun _ _ => rfl⟩
  rw [h.fibrationBoundary_mk hp]
  exact congrArg _ (GenLoop.ext _ _ fun _ => Subtype.ext (h.coe_topFace_apply _))

/-! ### Exactness -/

/-- **Exactness at `π_n(E, e₀)`.** A class in `π_n(E, e₀)` comes from the fibre `p⁻¹(p e₀)`
exactly when its image in `π_n(B, p e₀)` is trivial. -/
theorem mem_range_homotopyGroupMap_subtypeVal_iff [Finite N] (hp : serreFibrations p)
    {b : HomotopyGroup N E e₀} :
    b ∈ range (HomotopyGroup.map (x := (⟨e₀, rfl⟩ : p ⁻¹' {p e₀}))
      (ContinuousMap.subtypeVal (p ⁻¹' {p e₀})) rfl) ↔
      HomotopyGroup.map p.hom rfl b = (⟦GenLoop.const⟧ : HomotopyGroup N B (p e₀)) := by
  constructor
  · rintro ⟨a, rfl⟩
    induction a using Quotient.inductionOn with | h α => ?_
    have hα : GenLoop.map p.hom rfl (GenLoop.map (ContinuousMap.subtypeVal (p ⁻¹' {p e₀})) rfl α) =
        GenLoop.const :=
      GenLoop.ext _ _ fun y => (GenLoop.map_apply _ _ _ y).trans
        ((congrArg p.hom (GenLoop.map_apply _ _ α y)).trans (α y).2)
    exact (congrArg (HomotopyGroup.map p.hom rfl) (HomotopyGroup.map_mk _ _ α)).trans
      ((HomotopyGroup.map_mk _ _ _).trans (congrArg _ hα))
  · intro h
    induction b using Quotient.inductionOn with | h δ => ?_
    obtain ⟨K⟩ := Quotient.exact ((HomotopyGroup.map_mk _ _ δ).symm.trans h)
    -- Lift the null-homotopy `K` of `p ∘ δ`, starting at `δ` and fixed on the boundary.
    have hK (x : I × (I^N)) (hx : x ∈ cylinderExtensionDomain (Cube.boundary N)) :
        p (δ x.2) = K x := by
      rcases mem_cylinderExtensionDomain_iff.1 hx with h | h
      · rw [show x = (0, x.2) from Prod.ext h rfl, K.apply_zero]
        exact (GenLoop.map_apply _ _ _ _).symm
      · rw [show x = (x.1, x.2) from rfl, K.eq_fst _ h]
        exact (GenLoop.map_apply _ _ _ _).symm
    obtain ⟨L, hL, hLδ⟩ := exists_lift_openBox_of_mem_serreFibrations hp N
      ((δ : C(I^N, E)).comp ContinuousMap.snd |>.restrict _) K fun x => hK x.1 x.2
    have hL₁ (y : I^N) : p (L (1, y)) = p e₀ :=
      (congrFun hL (1, y)).trans (K.apply_one y)
    have hLδ' (x : I × (I^N)) (hx : x ∈ cylinderExtensionDomain (Cube.boundary N)) :
        L x = δ x.2 :=
      hLδ ⟨x, hx⟩
    -- The end of the lift is a cube in the fibre, homotopic to `δ` in `E` through the lift.
    let α : Ω^ N (p ⁻¹' {p e₀}) ⟨e₀, rfl⟩ :=
      ⟨⟨fun y => ⟨L (1, y), hL₁ y⟩, by fun_prop⟩, fun y hy =>
        Subtype.ext ((hLδ' _ (mem_cylinderExtensionDomain_of_mem hy)).trans (δ.2 y hy))⟩
    refine ⟨⟦α⟧, (HomotopyGroup.map_mk _ _ α).trans (Eq.symm (Quotient.sound ⟨{
      toFun := L
      map_zero_left := fun y => hLδ' _ (zero_mem_cylinderExtensionDomain y)
      map_one_left := fun y =>
        (GenLoop.map_apply (ContinuousMap.subtypeVal (p ⁻¹' {p e₀})) rfl α y).symm
      prop' := fun s y hy => hLδ' _ (mem_cylinderExtensionDomain_of_mem hy) }⟩))⟩

/-- **Exactness at `π_n(F, e₀)`.** A class in the homotopy group of the fibre `F = p⁻¹(p e₀)` is
a boundary exactly when it becomes trivial in `π_n(E, e₀)`. -/
theorem mem_range_fibrationBoundary_iff [Finite N] (hp : serreFibrations p)
    {a : HomotopyGroup N (p ⁻¹' {p e₀}) ⟨e₀, rfl⟩} :
    a ∈ range (fibrationBoundary hp e₀) ↔
      HomotopyGroup.map (ContinuousMap.subtypeVal (p ⁻¹' {p e₀})) rfl a =
        (⟦GenLoop.const⟧ : HomotopyGroup N E e₀) := by
  let e := piOptionEquivProdHomeomorph fun _ : Option N => I
  constructor
  · rintro ⟨b, rfl⟩
    induction b using Quotient.inductionOn with | h γ => ?_
    obtain ⟨G, hG⟩ := exists_isBoundaryLift hp γ
    rw [hG.fibrationBoundary_mk hp]
    have hG_one (y : I^N) :
        G (1, y) = GenLoop.map (ContinuousMap.subtypeVal (p ⁻¹' {p e₀})) rfl hG.topFace y :=
      (hG.coe_topFace_apply y).symm.trans
        (GenLoop.map_apply (ContinuousMap.subtypeVal _) rfl hG.topFace y).symm
    -- A boundary lift, run backwards, is a null-homotopy in `E` of its top face.
    refine (HomotopyGroup.map_mk _ _ _).trans (Quotient.sound ⟨{
      toFun := fun x => G (σ x.1, x.2)
      map_zero_left := fun y => ?_
      map_one_left := fun y => ?_
      prop' := fun s y hy => ?_ }⟩)
    · rw [symm_zero]
      exact hG_one y
    · rw [symm_one, hG.apply_zero]
      exact GenLoop.const_apply.symm
    · exact (hG.apply_of_mem _ hy).trans ((hG.apply_of_mem 1 hy).symm.trans (hG_one y))
  · intro h
    induction a using Quotient.inductionOn with | h α => ?_
    obtain ⟨K⟩ := Quotient.exact ((HomotopyGroup.map_mk _ _ α).symm.trans h)
    -- The null-homotopy `K` of `α` in `E`, run backwards, is a boundary lift of its projection.
    let G : C(I × (I^N), E) := ⟨fun x => K (σ x.1, x.2), by fun_prop⟩
    have hG_apply (x : I × (I^N)) : G x = K (σ x.1, x.2) := rfl
    have hG_zero (y : I^N) : G (0, y) = e₀ := by
      rw [hG_apply, symm_zero, K.apply_one]
      exact GenLoop.const_apply
    have hG_one (y : I^N) : G (1, y) = α y := by
      rw [hG_apply, symm_one, K.apply_zero]
      exact GenLoop.map_apply _ _ α y
    have hG_of_mem (t : I) {y : I^N} (hy : y ∈ Cube.boundary N) : G (t, y) = e₀ := by
      rw [hG_apply, K.eq_fst _ hy]
      exact (GenLoop.map_apply _ _ α y).trans (congrArg Subtype.val (α.2 y hy))
    have hG_eq (x : I × (I^N)) (hx : x ∈ cylinderExtensionDomain (Cube.boundary N)) :
        G x = e₀ := by
      rcases mem_cylinderExtensionDomain_iff.1 hx with h | h
      · rw [show x = (0, x.2) from Prod.ext h rfl, hG_zero]
      · exact hG_of_mem x.1 h
    have hG_proj (w : I^(Option N)) (hw : w ∈ Cube.boundary (Option N)) :
        p (G (e w)) = p e₀ := by
      rw [← piOptionEquivProdHomeomorph_mem_prodBoundary_iff, Cube.mem_prodBoundary_iff] at hw
      rcases hw with (h | h) | h
      · rw [hG_eq _ (mem_cylinderExtensionDomain_iff.2 (Or.inl h))]
      · rw [show e w = (1, (e w).2) from Prod.ext h rfl, hG_one]
        exact (α _).2
      · rw [hG_eq _ (mem_cylinderExtensionDomain_of_mem h)]
    let γ : Ω^ (Option N) B (p e₀) :=
      ⟨(p.hom.comp G).comp (e : C(I^(Option N), I × (I^N))), fun w hw => hG_proj w hw⟩
    have hγG : IsBoundaryLift p e₀ γ G :=
      ⟨fun x => by simp [γ, e], hG_eq⟩
    refine ⟨⟦γ⟧, ?_⟩
    rw [hγG.fibrationBoundary_mk hp]
    exact congrArg _ (GenLoop.ext _ _ fun y => Subtype.ext ((hγG.coe_topFace_apply y).trans
      (hG_one y)))

/-- **Exactness at `π_{n+1}(B, p e₀)`.** A class in `π_{n+1}(B, p e₀)` comes from `π_{n+1}(E, e₀)`
exactly when its boundary in the homotopy group of the fibre `p⁻¹(p e₀)` is trivial. -/
theorem mem_range_homotopyGroupMap_iff_fibrationBoundary_eq [Finite N] (hp : serreFibrations p)
    {a : HomotopyGroup (Option N) B (p e₀)} :
    a ∈ range (HomotopyGroup.map p.hom rfl) ↔
      fibrationBoundary hp e₀ a = ⟦GenLoop.const⟧ := by
  classical
  let e := piOptionEquivProdHomeomorph fun _ : Option N => I
  constructor
  · rintro ⟨b, rfl⟩
    induction b using Quotient.inductionOn with | h δ => ?_
    -- A cube in `E` is a boundary lift of its own projection, with constant top face.
    have hδ : IsBoundaryLift p e₀ (GenLoop.map p.hom rfl δ) ((δ : C(I^(Option N), E)).comp
        (e.symm : C(I × (I^N), I^(Option N)))) :=
      ⟨fun x => by simp [e], fun x hx => by simpa [e] using δ.2 _ (symm_mem_boundary_of_mem hx)⟩
    rw [HomotopyGroup.map_mk, hδ.fibrationBoundary_mk hp]
    exact congrArg _ (GenLoop.ext _ _ fun y => Subtype.ext (by
      simpa [e] using δ.2 _ (piOptionEquivProdHomeomorph_symm_mem_boundary
        (Cube.mk_mem_prodBoundary (.inl rfl)))))
  · intro h
    induction a using Quotient.inductionOn with | h γ => ?_
    obtain ⟨G, hG⟩ := exists_isBoundaryLift hp γ
    rw [hG.fibrationBoundary_mk hp] at h
    obtain ⟨K⟩ := Quotient.exact h
    -- Stack the null-homotopy `K` of the top face of `G` on top of `G`.
    have hK₀ (y : I^N) : (K (0, y) : E) = G (1, y) := by
      rw [K.apply_zero]
      exact hG.coe_topFace_apply y
    have hK_of_mem (s : I) {y : I^N} (hy : y ∈ Cube.boundary N) : (K (s, y) : E) = e₀ := by
      rw [K.eq_fst s hy]
      exact congrArg Subtype.val (hG.topFace.2 y hy)
    let δ' : C(I^(Option N), E) :=
      ⟨fun w => if (w none : ℝ) ≤ 1 / 2
        then G (projIcc 0 1 zero_le_one (2 * w none), fun i => w (some i))
        else (K (projIcc 0 1 zero_le_one (2 * w none - 1), fun i => w (some i)) : E), by
        refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const
          fun w hw => ?_
        rw [projIcc_eq_one.2 (by rw [hw]; norm_num), projIcc_eq_zero.2 (by rw [hw]; norm_num), hK₀]⟩
    have hδ'_le (w : I^(Option N)) (hw : (w none : ℝ) ≤ 1 / 2) :
        δ' w = G (projIcc 0 1 zero_le_one (2 * w none), fun i => w (some i)) := by
      simp only [δ', ContinuousMap.coe_mk, ite_eq_left hw]
    have hδ'_gt (w : I^(Option N)) (hw : ¬(w none : ℝ) ≤ 1 / 2) :
        δ' w = K (projIcc 0 1 zero_le_one (2 * w none - 1), fun i => w (some i)) := by
      simp only [δ', ContinuousMap.coe_mk, ite_eq_right hw]
    have hδ'_of_mem (w : I^(Option N)) (hw : w ∈ Cube.boundary (Option N)) : δ' w = e₀ := by
      rcases Cube.boundary_option_iff.1 hw with (h | h) | h
      · rw [hδ'_le w (by rw [h]; norm_num), h, projIcc_eq_zero.2 (by simp), hG.apply_zero]
      · rw [hδ'_gt w (by rw [h]; norm_num), h, projIcc_eq_one.2 (by norm_num), K.apply_one]
        exact congrArg Subtype.val GenLoop.const_apply
      · by_cases hw : (w none : ℝ) ≤ 1 / 2
        · rw [hδ'_le w hw, hG.apply_of_mem _ h]
        · rw [hδ'_gt w hw, hK_of_mem _ h]
    let δ : Ω^ (Option N) E e₀ := ⟨δ', hδ'_of_mem⟩
    -- The projection of the stacked cube is `γ` followed by the constant cube.
    have hδ : GenLoop.map p.hom rfl δ = GenLoop.transAt none γ GenLoop.const := by
      refine GenLoop.ext _ _ fun w => ?_
      rw [GenLoop.map_apply]
      by_cases hw : (w none : ℝ) ≤ 1 / 2
      · rw [GenLoop.transAt_apply_of_le none γ GenLoop.const hw
          (coe_projIcc_of_mem (mul_nonneg zero_le_two (w none).2.1) (by linarith)),
          update_none_eq_piOptionEquivProdHomeomorph_symm]
        exact (congrArg p.hom (hδ'_le w hw)).trans (hG.proj_apply _)
      · rw [GenLoop.transAt_apply_of_lt none γ GenLoop.const (lt_of_not_ge hw)
          (coe_projIcc_of_mem (by linarith) (by linarith [(w none).2.2])), GenLoop.const_apply]
        exact (congrArg p.hom (hδ'_gt w hw)).trans (K _).2
    refine ⟨⟦δ⟧, ?_⟩
    have hm := HomotopyGroup.mul_spec (X := B) (x := p e₀) (i := none) (p := GenLoop.const) (q := γ)
    beta_reduce at hm
    rw [HomotopyGroup.map_mk, hδ, ← hm, ← HomotopyGroup.one_def]
    exact one_mul _

/-! ### The boundary map is a homomorphism -/

/-- **The boundary map is multiplicative** in positive dimensions. Concatenating two cubes in a
direction of `I^N` concatenates their boundary lifts, and hence the top faces of these lifts. -/
theorem fibrationBoundary_mul [Finite N] [DecidableEq N] [Nonempty N] (hp : serreFibrations p)
    (a b : HomotopyGroup (Option N) B (p e₀)) :
    fibrationBoundary hp e₀ (a * b) = fibrationBoundary hp e₀ a * fibrationBoundary hp e₀ b := by
  induction a using Quotient.inductionOn with | h γ => ?_
  induction b using Quotient.inductionOn with | h δ => ?_
  let j := Classical.arbitrary N
  obtain ⟨Gγ, hγ⟩ := exists_isBoundaryLift hp γ
  obtain ⟨Gδ, hδ⟩ := exists_isBoundaryLift hp δ
  -- The coordinate `j` of a side, reparametrized onto either half, stays on a side.
  have hupd₀ {y : I^N} (hy : y ∈ Cube.boundary N) (hj : (y j : ℝ) ≤ 1 / 2) :
      Function.update y j (projIcc 0 1 zero_le_one (2 * y j)) ∈ Cube.boundary N := by
    obtain ⟨k, hk⟩ := hy
    by_cases hkj : k = j
    · subst hkj
      refine ⟨j, .inl ?_⟩
      rcases hk with hk | hk
      · rw [Function.update_self, hk, projIcc_eq_zero.2 (by simp)]
      · rw [hk] at hj
        norm_num at hj
    · exact ⟨k, by rwa [Function.update_of_ne hkj]⟩
  have hupd₁ {y : I^N} (hy : y ∈ Cube.boundary N) (hj : ¬(y j : ℝ) ≤ 1 / 2) :
      Function.update y j (projIcc 0 1 zero_le_one (2 * y j - 1)) ∈ Cube.boundary N := by
    obtain ⟨k, hk⟩ := hy
    by_cases hkj : k = j
    · subst hkj
      refine ⟨j, .inr ?_⟩
      rcases hk with hk | hk
      · rw [hk] at hj
        norm_num at hj
      · rw [Function.update_self, hk, projIcc_eq_one.2 (by norm_num)]
    · exact ⟨k, by rwa [Function.update_of_ne hkj]⟩
  -- The lift `Gδ` on the half `y j ≤ 1 / 2` and `Gγ` on the other half, both reparametrized.
  let G : C(I × (I^N), E) :=
    ⟨fun x => if (x.2 j : ℝ) ≤ 1 / 2
      then Gδ (x.1, Function.update x.2 j (projIcc 0 1 zero_le_one (2 * x.2 j)))
      else Gγ (x.1, Function.update x.2 j (projIcc 0 1 zero_le_one (2 * x.2 j - 1))), by
      refine Continuous.if_le (by fun_prop) (by fun_prop) (by fun_prop) continuous_const
        fun x hx => ?_
      rw [hδ.apply_of_mem _ ⟨j, .inr (by
          rw [Function.update_self, projIcc_eq_one.2 (by rw [hx]; norm_num)])⟩,
        hγ.apply_of_mem _ ⟨j, .inl (by
          rw [Function.update_self, projIcc_eq_zero.2 (by rw [hx]; norm_num)])⟩]⟩
  have hG_le (t : I) (y : I^N) (hy : (y j : ℝ) ≤ 1 / 2) :
      G (t, y) = Gδ (t, Function.update y j (projIcc 0 1 zero_le_one (2 * y j))) := by
    simp only [G, ContinuousMap.coe_mk, ite_eq_left hy]
  have hG_gt (t : I) (y : I^N) (hy : ¬(y j : ℝ) ≤ 1 / 2) :
      G (t, y) = Gγ (t, Function.update y j (projIcc 0 1 zero_le_one (2 * y j - 1))) := by
    simp only [G, ContinuousMap.coe_mk, ite_eq_right hy]
  have hcoe₀ {y : I^N} (hy : (y j : ℝ) ≤ 1 / 2) :
      (projIcc 0 1 zero_le_one (2 * (y j : ℝ)) : ℝ) = 2 * y j :=
    coe_projIcc_of_mem (mul_nonneg zero_le_two (y j).2.1) (by linarith)
  have hcoe₁ {y : I^N} (hy : ¬(y j : ℝ) ≤ 1 / 2) :
      (projIcc 0 1 zero_le_one (2 * (y j : ℝ) - 1) : ℝ) = 2 * y j - 1 :=
    coe_projIcc_of_mem (by linarith) (by linarith [(y j).2.2])
  have hG : IsBoundaryLift p e₀ (GenLoop.transAt (some j) δ γ) G := by
    refine ⟨fun ⟨t, y⟩ => ?_, fun ⟨t, y⟩ hx => ?_⟩
    · by_cases hy : (y j : ℝ) ≤ 1 / 2
      · rw [hG_le t y hy, hδ.proj_apply, GenLoop.transAt_apply_of_le (some j) δ γ
          (by simpa using hy) (a := projIcc 0 1 zero_le_one (2 * (y j : ℝ)))
          (by simpa using hcoe₀ hy), ← piOptionEquivProdHomeomorph_symm_update]
      · rw [hG_gt t y hy, hγ.proj_apply, GenLoop.transAt_apply_of_lt (some j) δ γ
          (by simpa using lt_of_not_ge hy) (a := projIcc 0 1 zero_le_one (2 * (y j : ℝ) - 1))
          (by simpa using hcoe₁ hy), ← piOptionEquivProdHomeomorph_symm_update]
    · rcases mem_cylinderExtensionDomain_iff.1 hx with (h : t = 0) | h
      · subst h
        by_cases hy : (y j : ℝ) ≤ 1 / 2
        · rw [hG_le 0 y hy, hδ.apply_zero]
        · rw [hG_gt 0 y hy, hγ.apply_zero]
      · by_cases hy : (y j : ℝ) ≤ 1 / 2
        · rw [hG_le t y hy, hδ.apply_of_mem _ (hupd₀ h hy)]
        · rw [hG_gt t y hy, hγ.apply_of_mem _ (hupd₁ h hy)]
  have hface : hG.topFace = GenLoop.transAt j hδ.topFace hγ.topFace := by
    refine GenLoop.ext _ _ fun y => Subtype.ext ?_
    rw [hG.coe_topFace_apply]
    by_cases hy : (y j : ℝ) ≤ 1 / 2
    · rw [hG_le 1 y hy, GenLoop.transAt_apply_of_le j _ _ hy (hcoe₀ hy), hδ.coe_topFace_apply]
    · rw [hG_gt 1 y hy, GenLoop.transAt_apply_of_lt j _ _ (lt_of_not_ge hy) (hcoe₁ hy),
        hγ.coe_topFace_apply]
  have hm := HomotopyGroup.mul_spec (X := B) (x := p e₀) (i := some j) (p := γ) (q := δ)
  beta_reduce at hm
  rw [hm, hG.fibrationBoundary_mk hp, hface, hγ.fibrationBoundary_mk hp,
    hδ.fibrationBoundary_mk hp]
  exact HomotopyGroup.mul_spec.symm

/-- The boundary map `π_{n+1}(B, p e₀) → π_n(F, e₀)` of a Serre fibration, as a group
homomorphism in positive dimensions. -/
def fibrationBoundaryHom [Finite N] [DecidableEq N] [Nonempty N] (hp : serreFibrations p)
    (e₀ : E) : HomotopyGroup (Option N) B (p e₀) →* HomotopyGroup N (p ⁻¹' {p e₀}) ⟨e₀, rfl⟩ where
  toFun := fibrationBoundary hp e₀
  map_one' := fibrationBoundary_const hp
  map_mul' := fibrationBoundary_mul hp

@[simp]
theorem fibrationBoundaryHom_apply [Finite N] [DecidableEq N] [Nonempty N]
    (hp : serreFibrations p) (a : HomotopyGroup (Option N) B (p e₀)) :
    fibrationBoundaryHom hp e₀ a = fibrationBoundary hp e₀ a :=
  (rfl)

end TauCeti.TopCat
