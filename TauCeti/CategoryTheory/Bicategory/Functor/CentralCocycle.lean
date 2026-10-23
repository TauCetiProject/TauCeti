/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.IsCommutative
public import Mathlib.CategoryTheory.Bicategory.Functor.LocallyDiscrete
public import Mathlib.CategoryTheory.Bicategory.NaturalTransformation.Pseudo
public import Mathlib.CategoryTheory.Center.Basic
public import Mathlib.CategoryTheory.SingleObj

/-!
# Central compositors of pseudofunctors and `2`-cocycles

Let a monoid `G` act on a category `C` by the identity functor at every `g : G`, and choose the
comparison isomorphisms of this action among the central automorphisms of `C`, that is, among
the units of the center `CatCenter C = End (𝟭 C)`. Such a choice is a function
`c : G × G → (CatCenter C)ˣ`, the compositor `T_(h * g) ≅ T_g ⋙ T_h` being `c (h, g)`. This file
shows that the coherence of the compositors has mathematical content: the associativity
condition is the multiplicative `2`-cocycle identity, and changing the identifications of the
transport functors with the identity by central units `b : G → (CatCenter C)ˣ` multiplies `c`
by the coboundary of `b`.

Since the center of `C` is commutative and the action functors are identities, `G` acts
trivially on the coefficients. The cocycle identity is therefore that of
`groupCohomology.IsMulCocycle₂` for the trivial action,
`c (g * h, j) * c (g, h) = c (h, j) * c (g, h * j)`, and the coboundary that of
`groupCohomology.IsMulCoboundary₂`. They are stated explicitly, since Mathlib has no
trivial-action instance on an arbitrary commutative group. The same identity, for central units
indexed by an additive monoid, is the associativity axiom of Mathlib's
`CategoryTheory.TwistShiftData`, which twists the compositors of a shift by central units.

## Main declarations

* `TauCeti.centralUnitIso C z`: the invertible `2`-cell of `Cat` on the identity functor of `C`
  whose components are those of the central unit `z`.
* `TauCeti.centralUnitIso_associativity_iff`: the associativity condition of a pseudofunctor out
  of `LocallyDiscrete (SingleObj G)` whose `1`-cells are identities and whose compositors are
  `centralUnitIso C (c (h, g))` holds at `(g, h, j)` if and only if `c` satisfies the `2`-cocycle
  identity there. `TauCeti.centralUnitIso_left_unitor_iff` and
  `TauCeti.centralUnitIso_right_unitor_iff` treat the unit conditions.
* `TauCeti.centralCocyclePseudofunctor c hc`: the pseudofunctor
  `LocallyDiscrete (SingleObj G) ⥤ᵖ Cat` attached to a `2`-cocycle `c`, with identity `1`-cells,
  compositors `c` and unit comparison `(c (1, 1))⁻¹`.
* `TauCeti.centralUnitIso_naturality_comp_iff`: the composition condition of a strong
  transformation with identity components and naturality `2`-cells `centralUnitIso C (b g)`
  between two such pseudofunctors holds if and only if the compositors differ by the coboundary
  of `b`.
* `TauCeti.centralCocycleStrongTrans b hb`: the resulting strong transformation
  `centralCocyclePseudofunctor c hc ⟶ centralCocyclePseudofunctor c' hc'` when
  `c' (g, h) = b g * b h / b (g * h) * c (g, h)`.

## References

Choices of transport functors whose composition isomorphisms need not be coherent, and the
resulting role of coherence for categorical actions, are discussed in

* Edward Frenkel, [Langlands Correspondence for Loop Groups](https://math.berkeley.edu/~frenkel/loop.pdf),
  §1.3.

The pseudofunctor and strong-transformation axioms are those of
* Niles Johnson and Donald Yau, *2-Dimensional Categories*, arXiv:2002.06055, Chapter 4.
-/

public section

universe w v u

open CategoryTheory Bicategory

open scoped IsMulCommutative

namespace CategoryTheory.Cat

/-- The associator of three identity functors in `Cat` is the identity. -/
@[simp]
lemma associator_id_hom (C : Type w) [Category.{v} C] :
    (α_ (𝟙 (Cat.of C)) (𝟙 (Cat.of C)) (𝟙 (Cat.of C))).hom = 𝟙 _ := by
  ext X
  simp

/-- The inverse associator of three identity functors in `Cat` is the identity. -/
@[simp]
lemma associator_id_inv (C : Type w) [Category.{v} C] :
    (α_ (𝟙 (Cat.of C)) (𝟙 (Cat.of C)) (𝟙 (Cat.of C))).inv = 𝟙 _ := by
  ext X
  simp

/-- The left unitor of the identity functor in `Cat` is the identity. -/
@[simp]
lemma leftUnitor_id_hom (C : Type w) [Category.{v} C] :
    (λ_ (𝟙 (Cat.of C))).hom = 𝟙 _ := by
  ext X
  simp

/-- The right unitor of the identity functor in `Cat` is the identity. -/
@[simp]
lemma rightUnitor_id_hom (C : Type w) [Category.{v} C] :
    (ρ_ (𝟙 (Cat.of C))).hom = 𝟙 _ := by
  ext X
  simp

/-- The inverse right unitor of the identity functor in `Cat` is the identity. -/
@[simp]
lemma rightUnitor_id_inv (C : Type w) [Category.{v} C] :
    (ρ_ (𝟙 (Cat.of C))).inv = 𝟙 _ := by
  ext X
  simp

end CategoryTheory.Cat

namespace TauCeti

section CentralUnitIso

variable (C : Type w) [Category.{v} C]

/-- The invertible `2`-cell of `Cat` on the identity functor of `C` given by a unit `z` of the
center of `C`: its components are the automorphisms `z.app X` of the objects `X` of `C`. -/
def centralUnitIso (z : (CatCenter C)ˣ) : 𝟙 (Cat.of C) ≅ 𝟙 (Cat.of C) :=
  Cat.Hom.isoMk (Aut.unitsEndEquivAut (𝟭 C) z).asIso

variable {C}

@[simp]
lemma centralUnitIso_hom_toNatTrans_app (z : (CatCenter C)ˣ) (X : C) :
    ((centralUnitIso C z).hom.toNatTrans.app X : X ⟶ X) = (z : CatCenter C).app X :=
  (rfl)

@[simp]
lemma centralUnitIso_inv_toNatTrans_app (z : (CatCenter C)ˣ) (X : C) :
    ((centralUnitIso C z).inv.toNatTrans.app X : X ⟶ X) = ((z⁻¹ : (CatCenter C)ˣ) :
      CatCenter C).app X :=
  (rfl)

lemma centralUnitIso_inv (z : (CatCenter C)ˣ) :
    (centralUnitIso C z).inv = (centralUnitIso C z⁻¹).hom :=
  (rfl)

/-- Right whiskering a central automorphism by the identity functor leaves it unchanged. -/
@[simp]
lemma centralUnitIso_hom_whiskerRight_id (z : (CatCenter C)ˣ) :
    (centralUnitIso C z).hom ▷ 𝟙 (Cat.of C) = (centralUnitIso C z).hom := by
  ext X
  simp

/-- Left whiskering a central automorphism by the identity functor leaves it unchanged. -/
@[simp]
lemma centralUnitIso_id_whiskerLeft_hom (z : (CatCenter C)ˣ) :
    𝟙 (Cat.of C) ◁ (centralUnitIso C z).hom = (centralUnitIso C z).hom := by
  ext X
  simp

@[simp]
lemma centralUnitIso_one : centralUnitIso C 1 = Iso.refl _ :=
  Iso.ext (rfl)

@[reassoc (attr := simp)]
lemma centralUnitIso_hom_comp_hom (z z' : (CatCenter C)ˣ) :
    (centralUnitIso C z).hom ≫ (centralUnitIso C z').hom = (centralUnitIso C (z * z')).hom := by
  ext X
  simp [CatCenter.mul_app]

@[simp]
lemma centralUnitIso_hom_inj {z z' : (CatCenter C)ˣ} :
    (centralUnitIso C z).hom = (centralUnitIso C z').hom ↔ z = z' := by
  refine ⟨fun h ↦ Units.ext (CatCenter.ext _ _ fun X ↦ ?_), fun h ↦ h ▸ rfl⟩
  simpa using congrArg (·.toNatTrans.app X) h

lemma centralUnitIso_hom_eq_id_iff {z : (CatCenter C)ˣ} :
    (centralUnitIso C z).hom = 𝟙 _ ↔ z = 1 := by
  rw [← centralUnitIso_hom_inj (z' := 1), centralUnitIso_one, Iso.refl_hom]

end CentralUnitIso

variable {G : Type u} [Monoid G] (C : Type w) [Category.{v} C]

/-- The associativity condition of a pseudofunctor out of `LocallyDiscrete (SingleObj G)` with
identity `1`-cells and central compositors `centralUnitIso C (c (h, g))` at `g ≫ h = h * g`,
evaluated at `(g, h, j)`, is the `2`-cocycle identity
`c (j * h, g) * c (j, h) = c (h, g) * c (j, h * g)` of `c` at `(j, h, g)`. -/
lemma centralUnitIso_associativity_iff (c : G × G → (CatCenter C)ˣ) (g h j : G) :
    (centralUnitIso C (c (j, h * g))).hom ≫ (centralUnitIso C (c (h, g))).hom ▷ 𝟙 (Cat.of C) ≫
        (α_ (𝟙 (Cat.of C)) (𝟙 (Cat.of C)) (𝟙 (Cat.of C))).hom ≫
          𝟙 (Cat.of C) ◁ (centralUnitIso C (c (j, h))).inv ≫
          (centralUnitIso C (c (j * h, g))).inv = 𝟙 _ ↔
      c (j * h, g) * c (j, h) = c (h, g) * c (j, h * g) := by
  simp only [centralUnitIso_inv, centralUnitIso_hom_whiskerRight_id,
    centralUnitIso_id_whiskerLeft_hom, Cat.associator_id_hom]
  rw [Category.id_comp]
  simp only [← Category.assoc, centralUnitIso_hom_comp_hom]
  rw [centralUnitIso_hom_eq_id_iff, mul_inv_eq_one, mul_inv_eq_iff_eq_mul,
    eq_comm, mul_comm (c (j, h * g)) (c (h, g))]

/-- The left unit condition of a pseudofunctor out of `LocallyDiscrete (SingleObj G)` with
identity `1`-cells, central compositors `centralUnitIso C (c (h, g))` at `g ≫ h = h * g` and
unit comparison `centralUnitIso C u`, evaluated at `g`, is `c (g, 1) * u = 1`. -/
lemma centralUnitIso_left_unitor_iff (c : G × G → (CatCenter C)ˣ) (u : (CatCenter C)ˣ) (g : G) :
    (centralUnitIso C (c (g, 1))).hom ≫ (centralUnitIso C u).hom ▷ 𝟙 (Cat.of C) ≫
        (λ_ (𝟙 (Cat.of C))).hom = 𝟙 _ ↔ c (g, 1) * u = 1 := by
  simp only [centralUnitIso_hom_whiskerRight_id, Cat.leftUnitor_id_hom,
    Category.comp_id, centralUnitIso_hom_comp_hom, centralUnitIso_hom_eq_id_iff]

/-- The right unit condition of a pseudofunctor out of `LocallyDiscrete (SingleObj G)` with
identity `1`-cells, central compositors `centralUnitIso C (c (h, g))` at `g ≫ h = h * g` and
unit comparison `centralUnitIso C u`, evaluated at `g`, is `c (1, g) * u = 1`. -/
lemma centralUnitIso_right_unitor_iff (c : G × G → (CatCenter C)ˣ) (u : (CatCenter C)ˣ)
    (g : G) :
    (centralUnitIso C (c (1, g))).hom ≫ 𝟙 (Cat.of C) ◁ (centralUnitIso C u).hom ≫
        (ρ_ (𝟙 (Cat.of C))).hom = 𝟙 _ ↔ c (1, g) * u = 1 := by
  simp only [centralUnitIso_id_whiskerLeft_hom, Cat.rightUnitor_id_hom,
    Category.comp_id, centralUnitIso_hom_comp_hom, centralUnitIso_hom_eq_id_iff]

/-- The pseudofunctor `LocallyDiscrete (SingleObj G) ⥤ᵖ Cat` attached to a `2`-cocycle `c` of
`G` with coefficients in the central units of `C`, for the trivial action. It sends the unique
object to `C` and every `g` to the identity functor; its composition comparison at
`g ≫ h = h * g` is `centralUnitIso C (c (h, g))`, and its unit comparison is
`centralUnitIso C (c (1, 1))⁻¹`. -/
@[expose] def centralCocyclePseudofunctor (c : G × G → (CatCenter C)ˣ)
    (hc : ∀ g h j : G, c (g * h, j) * c (g, h) = c (h, j) * c (g, h * j)) :
    LocallyDiscrete (SingleObj G) ⥤ᵖ Cat.{v, w} :=
  LocallyDiscrete.mkPseudofunctor (fun _ ↦ Cat.of C) (fun _ ↦ 𝟙 _)
    (fun _ ↦ centralUnitIso C (c (1, 1))⁻¹)
    (fun g h ↦ centralUnitIso C (c (h, g)))
    (fun g h j ↦ (centralUnitIso_associativity_iff C c g h j).2 (hc j h g))
    (fun g ↦ (centralUnitIso_left_unitor_iff C c _ g).2 (by
      -- The cocycle identity at `(g, 1, 1)` gives `c (g, 1) = c (1, 1)`.
      rw [show c (g, 1) = c (1, 1) by simpa using hc g 1 1, mul_inv_cancel]))
    (fun g ↦ (centralUnitIso_right_unitor_iff C c _ g).2 (by
      -- The cocycle identity at `(1, 1, g)` gives `c (1, g) = c (1, 1)`.
      rw [show c (1, g) = c (1, 1) by simpa [mul_comm] using (hc 1 1 g).symm, mul_inv_cancel]))

variable {C}

section Pseudofunctor

variable {c : G × G → (CatCenter C)ˣ}
  {hc : ∀ g h j : G, c (g * h, j) * c (g, h) = c (h, j) * c (g, h * j)}

@[simp]
lemma centralCocyclePseudofunctor_obj (a : LocallyDiscrete (SingleObj G)) :
    (centralCocyclePseudofunctor C c hc).obj a = Cat.of C :=
  (rfl)

@[simp]
lemma centralCocyclePseudofunctor_map {a b : LocallyDiscrete (SingleObj G)} (g : a ⟶ b) :
    (centralCocyclePseudofunctor C c hc).map g = 𝟙 (Cat.of C) :=
  (rfl)

@[simp]
lemma centralCocyclePseudofunctor_mapId (a : LocallyDiscrete (SingleObj G)) :
    (centralCocyclePseudofunctor C c hc).mapId a = centralUnitIso C (c (1, 1))⁻¹ :=
  (rfl)

@[simp]
lemma centralCocyclePseudofunctor_mapComp {a b d : LocallyDiscrete (SingleObj G)} (g : a ⟶ b)
    (h : b ⟶ d) :
    (centralCocyclePseudofunctor C c hc).mapComp g h = centralUnitIso C (c (h.as, g.as)) :=
  (rfl)

end Pseudofunctor

variable (C)

/-- The unit condition of a strong transformation with identity components and naturality
`2`-cells `centralUnitIso C (b g)`, between pseudofunctors with identity `1`-cells and unit
comparisons `centralUnitIso C u` and `centralUnitIso C u'`, is `b 1 * u' = u`. -/
lemma centralUnitIso_naturality_id_iff (b : G → (CatCenter C)ˣ) (u u' : (CatCenter C)ˣ) :
    (centralUnitIso C (b 1)).hom ≫ 𝟙 (Cat.of C) ◁ (centralUnitIso C u').hom =
        (centralUnitIso C u).hom ▷ 𝟙 (Cat.of C) ≫ (λ_ (𝟙 (Cat.of C))).hom ≫
          (ρ_ (𝟙 (Cat.of C))).inv ↔
      b 1 * u' = u := by
  simp only [centralUnitIso_hom_whiskerRight_id, centralUnitIso_id_whiskerLeft_hom,
    Cat.leftUnitor_id_hom, Cat.rightUnitor_id_inv, Category.comp_id,
    centralUnitIso_hom_comp_hom]
  rw [centralUnitIso_hom_inj]

/-- The composition condition of a strong transformation with identity components and
naturality `2`-cells `centralUnitIso C (b g)`, between pseudofunctors with identity `1`-cells
and central compositors `centralUnitIso C (c (h, g))` and `centralUnitIso C (c' (h, g))` at
`g ≫ h = h * g`, evaluated at `(g, h)`, states that `c'` is `c` multiplied by the coboundary of
`b` at `(h, g)`. -/
lemma centralUnitIso_naturality_comp_iff (b : G → (CatCenter C)ˣ) (c c' : G × G → (CatCenter C)ˣ)
    (g h : G) :
    (centralUnitIso C (b (h * g))).hom ≫ 𝟙 (Cat.of C) ◁ (centralUnitIso C (c' (h, g))).hom =
        (centralUnitIso C (c (h, g))).hom ▷ 𝟙 (Cat.of C) ≫
          (α_ (𝟙 (Cat.of C)) (𝟙 (Cat.of C)) (𝟙 (Cat.of C))).hom ≫
            𝟙 (Cat.of C) ◁ (centralUnitIso C (b h)).hom ≫
              (α_ (𝟙 (Cat.of C)) (𝟙 (Cat.of C)) (𝟙 (Cat.of C))).inv ≫
                (centralUnitIso C (b g)).hom ▷ 𝟙 (Cat.of C) ≫
                  (α_ (𝟙 (Cat.of C)) (𝟙 (Cat.of C)) (𝟙 (Cat.of C))).hom ↔
      c' (h, g) = b h * b g / b (h * g) * c (h, g) := by
  simp only [centralUnitIso_hom_whiskerRight_id, centralUnitIso_id_whiskerLeft_hom,
    Cat.associator_id_hom, Cat.associator_id_inv]
  simp only [Category.id_comp, Category.comp_id]
  simp only [← Category.assoc, centralUnitIso_hom_comp_hom]
  rw [centralUnitIso_hom_inj]
  have scalar_eq : (b (h * g))⁻¹ * (c (h, g) * b h * b g) =
      b h * b g / b (h * g) * c (h, g) := by
    rw [div_eq_mul_inv]
    ac_rfl
  rw [← eq_inv_mul_iff_mul_eq, scalar_eq]

variable {C}

/-- The strong transformation `centralCocyclePseudofunctor C c hc ⟶
centralCocyclePseudofunctor C c' hc'` with identity components whose naturality `2`-cell at `g`
is `centralUnitIso C (b g)`, when `c'` is `c` multiplied by the coboundary of
`b : G → (CatCenter C)ˣ`. By `centralUnitIso_naturality_comp_iff`, this coboundary relation is
also necessary for the identity components and the `2`-cells `centralUnitIso C (b g)` to form a
strong transformation. -/
@[expose] def centralCocycleStrongTrans {c c' : G × G → (CatCenter C)ˣ}
    {hc : ∀ g h j : G, c (g * h, j) * c (g, h) = c (h, j) * c (g, h * j)}
    {hc' : ∀ g h j : G, c' (g * h, j) * c' (g, h) = c' (h, j) * c' (g, h * j)}
    (b : G → (CatCenter C)ˣ) (hb : ∀ g h : G, c' (g, h) = b g * b h / b (g * h) * c (g, h)) :
    Pseudofunctor.StrongTrans (centralCocyclePseudofunctor C c hc)
      (centralCocyclePseudofunctor C c' hc') where
  app _ := 𝟙 (Cat.of C)
  naturality g := centralUnitIso C (b g.as)
  naturality_naturality η := by
    obtain rfl := LocallyDiscrete.eq_of_hom η
    rw [Subsingleton.elim η (𝟙 _)]
    ext X
    -- The whiskered identity `2`-cells have identity components, but only up to the
    -- definitional identification of `(centralCocyclePseudofunctor C c hc).map f` with `𝟙 _`.
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  naturality_id _ := (centralUnitIso_naturality_id_iff C b _ _).2 (by
    have hunit : c' (1, 1) = b 1 * c (1, 1) := by
      simpa only [one_mul, mul_div_cancel_right] using hb 1 1
    rw [hunit, mul_inv_rev]
    calc
      b 1 * ((c (1, 1))⁻¹ * (b 1)⁻¹) = (c (1, 1))⁻¹ * (b 1 * (b 1)⁻¹) := by ac_rfl
      _ = (c (1, 1))⁻¹ := by rw [mul_inv_cancel, mul_one])
  naturality_comp g h := (centralUnitIso_naturality_comp_iff C b c c' g.as h.as).2 (hb _ _)

@[simp]
lemma centralCocycleStrongTrans_app {c c' : G × G → (CatCenter C)ˣ}
    {hc : ∀ g h j : G, c (g * h, j) * c (g, h) = c (h, j) * c (g, h * j)}
    {hc' : ∀ g h j : G, c' (g * h, j) * c' (g, h) = c' (h, j) * c' (g, h * j)}
    (b : G → (CatCenter C)ˣ) (hb : ∀ g h : G, c' (g, h) = b g * b h / b (g * h) * c (g, h))
    (a : LocallyDiscrete (SingleObj G)) :
    (centralCocycleStrongTrans (hc := hc) (hc' := hc') b hb).app a = 𝟙 (Cat.of C) :=
  (rfl)

@[simp]
lemma centralCocycleStrongTrans_naturality {c c' : G × G → (CatCenter C)ˣ}
    {hc : ∀ g h j : G, c (g * h, j) * c (g, h) = c (h, j) * c (g, h * j)}
    {hc' : ∀ g h j : G, c' (g * h, j) * c' (g, h) = c' (h, j) * c' (g, h * j)}
    (b : G → (CatCenter C)ˣ) (hb : ∀ g h : G, c' (g, h) = b g * b h / b (g * h) * c (g, h))
    {a a' : LocallyDiscrete (SingleObj G)} (g : a ⟶ a') :
    (centralCocycleStrongTrans (hc := hc) (hc' := hc') b hb).naturality g =
      centralUnitIso C (b g.as) :=
  (rfl)

end TauCeti
