/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.CategoryTheory.Sites.CoversTop.Basic
public import Mathlib.CategoryTheory.Sites.Hypercover.One
public import Mathlib.CategoryTheory.Sites.LocallySurjective
public import TauCeti.AlgebraicTopology.SimplicialObject.Hypercover
public import TauCeti.CategoryTheory.Sites.Limits

/-!
# The `1`-hypercover of a site given by a simplicial hypercover of sheaves

Let `U` be a simplicial object in the category of sheaves of types on a site `(C, J)`, which is a
hypercover of the terminal sheaf (`CategoryTheory.SimplicialObject.IsHypercover`). Its degrees `0`
and `1` determine, for every `S : C`, a `1`-hypercover of `S` in the sense of Mathlib
(`CategoryTheory.GrothendieckTopology.OneHypercover`), with representable covering objects.

* `CategoryTheory.SimplicialObject.preOneHypercover`: the covering family of `S` consists of all
  sections `x` of `U _⦋0⦌` over objects `T` over `S`. For two such sections `x₁` over `T₁` and
  `x₂` over `T₂`, the covering family of `T₁ ×_S T₂` consists of all sections `y` of `U _⦋1⦌`
  over objects `W` with maps `W ⟶ T₁` and `W ⟶ T₂` over `S` along which `x₁` and `x₂` restrict
  to the vertices `δ 1 y` and `δ 0 y`. This needs no hypothesis on `U`.
* `CategoryTheory.SimplicialObject.IsHypercover.oneHypercover`: when `U` is a hypercover, these
  families are covering, so they form a `1`-hypercover of `S`.

The two covering conditions come from the two conditions in degrees `0` and `1` of a hypercover,
read through local surjectivity of epimorphisms of sheaves (`Sheaf.isLocallySurjective_iff_epi`).
The objects carrying a section of `U _⦋0⦌` cover the terminal object
(`CategoryTheory.SimplicialObject.IsHypercover.coversTop`). Locally, any two sections of
`U _⦋0⦌` are the two vertices of a section of `U _⦋1⦌`
(`CategoryTheory.SimplicialObject.IsHypercover.locally_exists_δ_eq`), because the degree-one
matching object is `U _⦋0⦌ ⨯ U _⦋0⦌` (`CategoryTheory.SimplicialObject.matchingObjectZeroIso`).

## References

* M. Artin, A. Grothendieck and J.-L. Verdier, *Théorie des topos et cohomologie étale des
  schémas* (SGA 4), Lecture Notes in Mathematics 270, Springer, 1972, Exposé V, §7.
* B. Bhatt and P. Scholze, *The pro-étale topology for schemes*, Astérisque 369 (2015), 99–201,
  Proposition 3.3.6 and the notation following it.
-/

public section

open CategoryTheory Limits Opposite

open scoped Simplicial

universe w v u

namespace CategoryTheory.SimplicialObject

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  (U : SimplicialObject (Sheaf J (Type w)))

/-- The pre-`1`-hypercover of `S : C` given by the sections of a simplicial sheaf `U` in degrees `0`
and `1`. Its covering family consists of the sections of `U _⦋0⦌` over objects over `S`. For two
of them, `x₁` over `T₁` and `x₂` over `T₂`, the covering family of their fibre product consists
of the sections `y` of `U _⦋1⦌` over objects `W` with maps `W ⟶ T₁` and `W ⟶ T₂` over `S` along
which `x₁` and `x₂` restrict to `δ 1 y` and `δ 0 y`. -/
@[expose, simps]
def preOneHypercover (S : C) : PreOneHypercover.{max u v w} S where
  I₀ := Σ T : Over S, (U _⦋0⦌).obj.obj (op T.left)
  X i := i.1.left
  f i := i.1.hom
  I₁ i₁ i₂ := Σ W : C, { p : (W ⟶ i₁.1.left) × (W ⟶ i₂.1.left) × (U _⦋1⦌).obj.obj (op W) //
    p.1 ≫ i₁.1.hom = p.2.1 ≫ i₂.1.hom ∧
    (U.δ 1).hom.app (op W) p.2.2 = (U _⦋0⦌).obj.map p.1.op i₁.2 ∧
    (U.δ 0).hom.app (op W) p.2.2 = (U _⦋0⦌).obj.map p.2.1.op i₂.2 }
  Y _ _ j := j.1
  p₁ _ _ j := j.2.1.1
  p₂ _ _ j := j.2.1.2.1
  w _ _ j := j.2.2.1

variable [HasSheafify J (Type w)] [U.IsHypercover]

/-- The objects of `C` over which `U _⦋0⦌` has a section cover the terminal object. -/
theorem IsHypercover.coversTop :
    J.CoversTop (fun i : Σ T : C, (U _⦋0⦌).obj.obj (op T) ↦ i.1) := by
  intro S
  let hT := Sheaf.isTerminalTerminal J Types.isTerminalPUnit.{w}
  have : Sheaf.IsLocallySurjective (hT.from (U _⦋0⦌)) := by
    rw [Sheaf.isLocallySurjective_iff_epi, hT.hom_ext (hT.from _)
      (terminal.from _ ≫ (terminalIsoIsTerminal hT).hom)]
    infer_instance
  refine J.superset_covering ?_ (Presheaf.imageSieve_mem J (hT.from (U _⦋0⦌)).hom
    (PUnit.unit : (Sheaf.terminal J Types.isTerminalPUnit).obj.obj (op S)))
  rintro T g ⟨x, -⟩
  exact ⟨⟨T, x⟩, ⟨𝟙 T⟩⟩

/-- Locally on `W`, any two sections `a` and `b` of `U _⦋0⦌` over `W` are the vertices `δ 1` and
`δ 0` of a section of `U _⦋1⦌`. -/
theorem IsHypercover.locally_exists_δ_eq {W : C} (a b : (U _⦋0⦌).obj.obj (op W)) :
    ∃ R ∈ J W, ∀ ⦃Z : C⦄ (g : Z ⟶ W), R g → ∃ y : (U _⦋1⦌).obj.obj (op Z),
      (U.δ 1).hom.app (op Z) y = (U _⦋0⦌).obj.map g.op a ∧
        (U.δ 0).hom.app (op Z) y = (U _⦋0⦌).obj.map g.op b := by
  let φ := prod.lift (U.δ (n := 0) 1) (U.δ 0)
  have : Sheaf.IsLocallySurjective φ := by
    rw [Sheaf.isLocallySurjective_iff_epi, ← epi_matchingMap_zero_iff]
    infer_instance
  obtain ⟨e, he₁, he₂⟩ := Sheaf.exists_fst_eq_snd_eq a b
  refine ⟨_, Presheaf.imageSieve_mem J φ.hom e, fun Z g ⟨y, hy⟩ ↦ ?_⟩
  -- Composing `φ` with a map out of `U _⦋0⦌ ⨯ U _⦋0⦌` transports `hy`.
  have h (f : U _⦋0⦌ ⨯ U _⦋0⦌ ⟶ U _⦋0⦌) :
      (φ ≫ f).hom.app (op Z) y = (U _⦋0⦌).obj.map g.op (f.hom.app (op W) e) := by
    simp [hy, NatTrans.naturality_apply]
  exact ⟨y, by simpa [φ, he₁] using h prod.fst, by simpa [φ, he₂] using h prod.snd⟩

/-- The `1`-hypercover of `S : C` given by the sections in degrees `0` and `1` of a hypercover `U`
of the terminal sheaf, with underlying pre-`1`-hypercover `U.preOneHypercover S`. -/
noncomputable def IsHypercover.oneHypercover (S : C) : J.OneHypercover S where
  toPreOneHypercover := U.preOneHypercover S
  mem₀ := by
    refine J.superset_covering ?_ (IsHypercover.coversTop U S)
    rintro T g ⟨⟨T', x⟩, ⟨h⟩⟩
    exact Sieve.ofArrows_mk _ _
      (⟨Over.mk g, (U _⦋0⦌).obj.map h.op x⟩ : (U.preOneHypercover S).I₀)
  mem₁ i₁ i₂ W p₁ p₂ w := by
    obtain ⟨R, hR, hy⟩ := IsHypercover.locally_exists_δ_eq U
      ((U _⦋0⦌).obj.map p₁.op i₁.2) ((U _⦋0⦌).obj.map p₂.op i₂.2)
    refine J.superset_covering ?_ hR
    intro Z g hg
    obtain ⟨y, hy₁, hy₂⟩ := hy g hg
    refine ⟨⟨Z, (g ≫ p₁, g ≫ p₂, y),
      (Category.assoc _ _ _).trans ((g ≫= w).trans (Category.assoc _ _ _).symm), ?_, ?_⟩, 𝟙 Z,
      (Category.id_comp _).symm, (Category.id_comp _).symm⟩
    · exact hy₁.trans (Functor.map_comp_apply (U _⦋0⦌).obj p₁.op g.op i₁.2).symm
    · exact hy₂.trans (Functor.map_comp_apply (U _⦋0⦌).obj p₂.op g.op i₂.2).symm

/-- The underlying pre-`1`-hypercover of `IsHypercover.oneHypercover U S` is
`U.preOneHypercover S`. -/
@[simp]
theorem IsHypercover.oneHypercover_toPreOneHypercover (S : C) :
    (IsHypercover.oneHypercover U S).toPreOneHypercover = U.preOneHypercover S := (rfl)

end CategoryTheory.SimplicialObject
