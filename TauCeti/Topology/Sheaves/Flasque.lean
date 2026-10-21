/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Homology.Ext.Basic
public import TauCeti.CategoryTheory.Sites.SheafCohomology.FreeYoneda
public import TauCeti.CategoryTheory.Sites.SheafCohomology.Terminal
public import Mathlib.CategoryTheory.Abelian.GrothendieckCategory.HasExt
public import Mathlib.Topology.Sheaves.Abelian
public import Mathlib.Topology.Sheaves.Flasque
public import Mathlib.Topology.Sheaves.Skyscraper

/-!
# Flasque sheaves: locality and acyclicity

A sheaf on a topological space is flasque when all of its restriction maps are surjective. This
file proves that flasqueness is a local property, and that a flasque sheaf of abelian groups has
no higher cohomology.

## Main declarations

* `TopCat.Sheaf.map_surjective_of_locally_flasque`: if every point has an open neighbourhood `W`
  such that all restriction maps between opens contained in `W` are surjective, then all
  restriction maps are surjective. It holds for sheaves valued in any concrete category in which
  sections glue (for instance sets, abelian groups and modules);
* `TopCat.Sheaf.isFlasque_of_locally_flasque`: the same statement, with the conclusion phrased
  by Mathlib's `TopCat.Sheaf.IsFlasque`;

* `TauCeti.Topology.isFlasque_of_injective`: an injective object in the category of abelian
  sheaves is flasque;
* `TauCeti.Topology.subsingleton_H'_succ_of_isFlasque`: a flasque sheaf has vanishing
  cohomology in every positive degree over every open subset;
* `TauCeti.Topology.subsingleton_H_succ_of_isFlasque`: the same statement for the cohomology
  of the whole space;
* `TauCeti.Topology.isFlasque_skyscraperSheaf`: skyscraper sheaves are flasque, and hence acyclic.

Locality is proved by Zorn's lemma. Fix `U ≤ V` and a section `s` over `U`, and order the
extensions of `s` to opens between `U` and `V` by extension. A chain of extensions glues to an
extension over the union of their domains, so there is a maximal extension. If a point `x` of `V`
lay outside its domain `O`, take a neighbourhood `W` of `x` on which `F` is flasque: the
restriction of the section to `O ⊓ W ⊓ V` lifts to `W ⊓ V`, and the two glue to a strictly larger
extension. Mathlib's proof of `TopCat.Sheaf.IsFlasque.epi_of_shortExact` is a Zorn argument of
the same shape.

Acyclicity is proved by the classical dimension shift. Embedding a flasque sheaf `F` in an injective
sheaf `I` gives a short exact sequence `0 ⟶ F ⟶ I ⟶ Q ⟶ 0`, and the covariant long exact sequence of
`Ext` presents `Hⁿ⁺¹(U, F)` as a quotient of `Hⁿ(U, Q)`. In degree zero, the sections of `Q` over
`U` lift to sections of `I` because `F` is flasque, so the quotient vanishes; in higher degrees `Q`
is again flasque, because `I` is, and induction applies. That `I` is flasque is the point at which
`TauCeti/CategoryTheory/Sites/SheafCohomology/FreeYoneda.lean` enters: an inclusion of open subsets
induces a monomorphism of the free abelian sheaves they generate, and `Hom(-, I)` turns it into the
restriction map of `I`.

This advances `TauCetiRoadmap/JacobianChallenge/README.md`, Layer B, "coherent sheaves and
cohomology `Hⁱ(X, ℱ)`: acyclicity of affines, …, vanishing above dimension": it is the first
acyclicity theorem of the lane, and the acyclic skyscraper sheaves are the coefficients in which
the Riemann-Roch induction over the points of a divisor reads the additivity of
`TauCeti/AlgebraicGeometry/Cohomology/EulerCharacteristic.lean`.

No formalization is vendored: flasqueness, the surjectivity of sections out of a flasque
subsheaf, the stability of flasqueness under quotients and the flasqueness of skyscraper sheaves
are Mathlib's `Mathlib/Topology/Sheaves/Flasque.lean`, and the long exact sequence is Mathlib's
`CategoryTheory.Abelian.Ext.covariant_sequence_exact₁`.

## References

* G. E. Bredon, *Sheaf Theory*, 2nd ed., Graduate Texts in Mathematics 170, Section II.5.
* R. Hartshorne, *Algebraic Geometry*, III.2.4–2.5.
* The Stacks Project, tag 09SY, Lemma 20.12.3, *Flasque sheaves*.
-/

public section

open CategoryTheory Limits Opposite TopologicalSpace
open TauCeti.CategoryTheory (freeYonedaSheafFunctor freeYonedaSheafSectionsEquiv sheafH'_eq
  freeYonedaSheafSectionsEquiv_naturality_left freeYonedaSheafSectionsEquiv_naturality_right)

universe u

namespace TauCeti

namespace Topology

variable {X : TopCat.{u}}

noncomputable section

/-- An injective object in the category of sheaves of abelian groups is flasque. -/
instance isFlasque_of_injective
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) [Injective F] :
    TopCat.Presheaf.IsFlasque F.obj where
  -- Given `s : I(V)` and `V ≤ U`, represent `s` by `ℤ_V ⟶ I`, extend it along the
  -- monomorphism `ℤ_V ⟶ ℤ_U` using injectivity, and translate the extension back to a section.
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    intro s
    refine ⟨freeYonedaSheafSectionsEquiv _ U.unop F
      (Injective.factorThru ((freeYonedaSheafSectionsEquiv _ V.unop F).symm s)
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).map i.unop)), ?_⟩
    have h := freeYonedaSheafSectionsEquiv_naturality_left
      (Opens.grothendieckTopology X) i.unop F
      (Injective.factorThru ((freeYonedaSheafSectionsEquiv _ V.unop F).symm s)
        ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).map i.unop))
    rw [Injective.comp_factorThru, AddEquiv.apply_symm_apply] at h
    exact h.symm

private instance isFlasque_injectiveCokernelSequence_X₂
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}) :
    TopCat.Presheaf.IsFlasque (injectiveCokernelSequence F).X₂.obj :=
  isFlasque_of_injective _

/-- The dimension-shifting induction: a flasque sheaf has no cohomology in positive degrees over
any open subset. -/
private lemma subsingleton_H'_succ_of_isFlasque_aux (n : ℕ) :
    ∀ (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u}),
      TopCat.Presheaf.IsFlasque F.obj → ∀ U : Opens X,
      Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) := by
  induction n with
  | zero =>
    intro F hF U
    rw [sheafH'_eq]
    apply subsingleton_ext_succ_of_injectiveCokernelSequence
    intro x₃
    let S := injectiveCokernelSequence F
    have hS₁ : TopCat.Presheaf.IsFlasque S.X₁.obj := by dsimp [S]; exact hF
    let _ : TopCat.Presheaf.IsFlasque S.X₁.obj := hS₁
    have hS := injectiveCokernelSequence_shortExact F
    have hepi : Epi (S.g.hom.app (op U)) :=
      TopCat.Sheaf.IsFlasque.epi_of_shortExact hS
    rw [AddCommGrpCat.epi_iff_surjective] at hepi
    obtain ⟨t, ht⟩ := hepi
      (freeYonedaSheafSectionsEquiv _ U S.X₃ (Abelian.Ext.addEquiv₀ x₃))
    have hx₃ : x₃ =
        (Abelian.Ext.mk₀ ((freeYonedaSheafSectionsEquiv _ U S.X₂).symm t)).comp
        (Abelian.Ext.mk₀ S.g) (add_zero 0) := by
      rw [Abelian.Ext.mk₀_comp_mk₀]
      refine (Abelian.Ext.mk₀_addEquiv₀_apply x₃).symm.trans (congrArg Abelian.Ext.mk₀ ?_)
      refine (freeYonedaSheafSectionsEquiv _ U S.X₃).injective ?_
      rw [freeYonedaSheafSectionsEquiv_naturality_right, AddEquiv.apply_symm_apply, ht]
    rw [hx₃, Abelian.Ext.comp_assoc_of_second_deg_zero, hS.comp_extClass,
      Abelian.Ext.comp_zero]
  | succ n ih =>
    intro F hF U
    rw [sheafH'_eq]
    apply subsingleton_ext_succ_of_injectiveCokernelSequence
    intro x₃
    let S := injectiveCokernelSequence F
    have hS₁ : TopCat.Presheaf.IsFlasque S.X₁.obj := by dsimp [S]; exact hF
    let _ : TopCat.Presheaf.IsFlasque S.X₁.obj := hS₁
    have hS := injectiveCokernelSequence_shortExact F
    have hS₃ : TopCat.Presheaf.IsFlasque S.X₃.obj :=
      TopCat.Sheaf.IsFlasque.of_shortExact_of_isFlasque₁₂ hS
    have hH : Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} S.X₃ (n + 1) U) :=
      ih S.X₃ hS₃ U
    have hExt : Subsingleton
        (Abelian.Ext.{u}
          ((freeYonedaSheafFunctor (Opens.grothendieckTopology X)).obj U) S.X₃ (n + 1)) :=
      by simpa only [sheafH'_eq] using hH
    rw [@Subsingleton.elim _ hExt x₃ 0, Abelian.Ext.zero_comp]

/-- A flasque sheaf of abelian groups has vanishing cohomology in every positive degree over
every open subset. -/
instance subsingleton_H'_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) (U : Opens X) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H'.{u} F (n + 1) U) :=
  subsingleton_H'_succ_of_isFlasque_aux n F inferInstance U

/-- A flasque sheaf of abelian groups has vanishing cohomology in every positive degree. -/
instance subsingleton_H_succ_of_isFlasque
    (F : Sheaf (Opens.grothendieckTopology X) AddCommGrpCat.{u})
    [TopCat.Presheaf.IsFlasque F.obj] (n : ℕ) :
    Subsingleton (_root_.CategoryTheory.Sheaf.H.{u} F (n + 1)) := by
  have := subsingleton_H'_succ_of_isFlasque F n (⊤ : Opens X)
  exact Function.Injective.subsingleton
    (f := ConcreteCategory.hom
      (F.cohomologyPresheafObjIsoH (n + 1) isTerminalTop).inv)
    ((ConcreteCategory.bijective_of_isIso _).injective)

/-- A skyscraper sheaf of abelian groups is flasque. -/
instance isFlasque_skyscraperSheaf (p₀ : X) (A : AddCommGrpCat.{u})
    [(U : Opens X) → Decidable (p₀ ∈ U)] :
    TopCat.Presheaf.IsFlasque (skyscraperSheaf p₀ A).obj :=
  isFlasque_skyscraperSheaf_of_hasZeroObject p₀ A

end

end Topology

end TauCeti

namespace TopCat.Sheaf

variable {C : Type*} [Category* C] {FC : C → C → Type*} {CC : C → Type*}
  [∀ X Y, FunLike (FC X Y) (CC X) (CC Y)] [ConcreteCategory C FC]
  {X : TopCat.{u}} (F : X.Sheaf C)

/-- An extension of a section `s` over `U` to an open set between `U` and `V`. These are the
objects ordered by the Zorn argument proving `TopCat.Sheaf.map_surjective_of_locally_flasque`. -/
private structure FlasqueExtension {U V : Opens X} (s : ToType (F.1.obj (op U))) where
  /-- The domain of the extended section. -/
  dom : Opens X
  le_dom : U ≤ dom
  dom_le : dom ≤ V
  /-- The extended section. -/
  val : ToType (F.1.obj (op dom))
  map_val : F.1.map (homOfLE le_dom).op val = s

namespace FlasqueExtension

variable {F} {U V : Opens X} {s : ToType (F.1.obj (op U))}

/- Morphisms in `Opens X` are proofs of `≤`, so any two parallel restriction maps of `F` are
equal by `rfl`. The proofs below use this after composing restrictions with
`Functor.map_comp_apply`. -/

/-- `p.Le q` means that `q` extends `p`. -/
private def Le (p q : FlasqueExtension F (V := V) s) : Prop :=
  ∃ h : p.dom ≤ q.dom, F.1.map (homOfLE h).op q.val = p.val

private lemma Le.trans {p q r : FlasqueExtension F (V := V) s} (hpq : p.Le q) (hqr : q.Le r) :
    p.Le r := by
  obtain ⟨h₁, e₁⟩ := hpq
  obtain ⟨h₂, e₂⟩ := hqr
  exact ⟨h₁.trans h₂, by rw [← e₁, ← e₂, ← Functor.map_comp_apply]; rfl⟩

variable [HasLimitsOfSize.{u, u} C] [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]

/-- A chain of extensions has an upper bound: glue the sections along the union of their
domains. -/
private lemma exists_le_of_isChain (hUV : U ≤ V) (c : Set (FlasqueExtension F (V := V) s))
    (hc : IsChain Le c) : ∃ ub, ∀ p ∈ c, p.Le ub := by
  rcases c.eq_empty_or_nonempty with rfl | ⟨p₀, hp₀⟩
  · exact ⟨⟨U, le_rfl, hUV, s, by simp⟩, by simp⟩
  let O : c → Opens X := fun p ↦ p.1.dom
  obtain ⟨t, ht, -⟩ := F.existsUnique_gluing O (fun p ↦ p.1.val) fun p q ↦ by
    by_cases hpq : p = q
    · subst hpq; rfl
    rcases hc p.2 q.2 (fun h ↦ hpq (Subtype.ext h)) with ⟨h, e⟩ | ⟨h, e⟩ <;>
      dsimp only <;> rw [← e, ← Functor.map_comp_apply] <;> rfl
  refine ⟨⟨iSup O, p₀.le_dom.trans (le_iSup O ⟨p₀, hp₀⟩), iSup_le fun p ↦ p.1.dom_le, t, ?_⟩,
    fun p hp ↦ ⟨le_iSup O ⟨p, hp⟩, ht ⟨p, hp⟩⟩⟩
  refine Eq.trans ?_ p₀.map_val
  have h₀ := ht ⟨p₀, hp₀⟩
  dsimp only at h₀
  rw [← h₀, ← Functor.map_comp_apply]
  rfl

/-- An extension can be enlarged across `W ⊓ V` whenever `F` is flasque on `W`: lift the
restriction of its section to the overlap, then glue. -/
private lemma exists_le_inf_le (p : FlasqueExtension F (V := V) s) {W : Opens X}
    (hW : ∀ ⦃A B : Opens X⦄ (hAB : A ≤ B), B ≤ W →
      Function.Surjective (F.1.map (homOfLE hAB).op)) :
    ∃ q : FlasqueExtension F (V := V) s, p.Le q ∧ W ⊓ V ≤ q.dom := by
  obtain ⟨t, ht⟩ := hW (inf_le_right : p.dom ⊓ (W ⊓ V) ≤ W ⊓ V) inf_le_left
    (F.1.map (homOfLE inf_le_left : p.dom ⊓ (W ⊓ V) ⟶ p.dom).op p.val)
  have key {D : Opens X} (hA : D ≤ p.dom) (hB : D ≤ W ⊓ V) :
      F.1.map (homOfLE hA).op p.val = F.1.map (homOfLE hB).op t := by
    have := congrArg (F.1.map (homOfLE (le_inf hA hB)).op) ht
    rw [← Functor.map_comp_apply, ← Functor.map_comp_apply] at this
    exact this.symm
  let O : Fin 2 → Opens X := ![p.dom, W ⊓ V]
  let sf : ∀ i, ToType (F.1.obj (op (O i)))
    | 0 => p.val
    | 1 => t
  obtain ⟨g, hg, -⟩ := F.existsUnique_gluing O sf fun i j ↦ by
    fin_cases i <;> fin_cases j
    exacts [rfl, key _ _, (key _ _).symm, rfl]
  refine ⟨⟨iSup O, p.le_dom.trans (le_iSup O 0),
    iSup_le (Fin.forall_fin_two.2 ⟨p.dom_le, inf_le_right⟩), g, ?_⟩, ⟨le_iSup O 0, hg 0⟩,
    le_iSup O 1⟩
  refine Eq.trans ?_ p.map_val
  have h₀ : F.1.map (homOfLE (le_iSup O 0) : p.dom ⟶ iSup O).op g = p.val := hg 0
  rw [← h₀, ← Functor.map_comp_apply]
  rfl

end FlasqueExtension

variable [HasLimitsOfSize.{u, u} C] [(CategoryTheory.forget C).ReflectsIsomorphisms]
  [PreservesLimitsOfSize.{u, u} (CategoryTheory.forget C)]

/-- **Flasque locality.** If every point of `X` has an open neighbourhood `W` such that every
restriction map `F(B) → F(A)` of `F` with `A ≤ B ≤ W` is surjective, then every restriction map
of `F` is surjective.

For `C = Type u` this is the statement for sheaves of sets. -/
theorem map_surjective_of_locally_flasque
    (hF : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ ⦃A B : Opens X⦄ (hAB : A ≤ B), B ≤ W →
      Function.Surjective (F.1.map (homOfLE hAB).op))
    {U V : Opens X} (hUV : U ≤ V) : Function.Surjective (F.1.map (homOfLE hUV).op) := by
  intro s
  -- By Zorn's lemma, `s` has a maximal extension `m` to an open between `U` and `V`.
  obtain ⟨m, hm⟩ := exists_maximal_of_chains_bounded
    (FlasqueExtension.exists_le_of_isChain (F := F) (s := s) hUV) FlasqueExtension.Le.trans
  -- Maximality and the local hypothesis force the domain of `m` to contain `V`.
  have hV : V ≤ m.dom := fun x hx ↦ by
    obtain ⟨W, hxW, hW⟩ := hF x
    obtain ⟨q, hmq, hq⟩ := m.exists_le_inf_le hW
    exact (hm q hmq).1 (hq ⟨hxW, hx⟩)
  refine ⟨F.1.map (homOfLE hV).op m.val, ?_⟩
  rw [← Functor.map_comp_apply]
  exact m.map_val

/-- **Flasque locality**, with the conclusion phrased by Mathlib's `TopCat.Sheaf.IsFlasque`: a
sheaf all of whose restriction maps between opens inside some neighbourhood of each point are
surjective is flasque. -/
theorem isFlasque_of_locally_flasque
    (hF : ∀ x : X, ∃ W : Opens X, x ∈ W ∧ ∀ ⦃A B : Opens X⦄ (hAB : A ≤ B), B ≤ W →
      Function.Surjective (F.1.map (homOfLE hAB).op)) :
    F.IsFlasque where
  epi i := ConcreteCategory.epi_of_surjective _ (F.map_surjective_of_locally_flasque hF i.unop.le)

end TopCat.Sheaf
