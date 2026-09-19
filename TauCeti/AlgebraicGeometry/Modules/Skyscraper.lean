/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.Cohomology.Flasque
public import TauCeti.AlgebraicGeometry.ResidueDegree

/-!
# The skyscraper sheaf of a residue field

For a point `x` of a scheme `X`, the skyscraper sheaf `κ(x)ₓ` has sections `κ(x)` over the open
subsets containing `x` and `0` over the others, a regular function `r` acting through its value
`r(x) ∈ κ(x)`. This file realizes it as the pushforward of the structure sheaf along the canonical
morphism `Spec κ(x) ⟶ X`, which makes the sheaf condition and the `𝒪_X`-module structure
automatic, and computes its cohomology: it is flasque, hence acyclic in positive degrees, and its
zeroth cohomology over a base field `k` has dimension `[κ(x) : k]`.

Skyscraper sheaves of residue fields are the cokernels of the inclusions `𝒪_X(D) ⟶ 𝒪_X(D + x)` of
divisor sheaves on a curve, which is how the Euler characteristic of a divisor sheaf changes by
`[κ(x) : k]` when a point is added to the divisor.

## Main declarations

* `Scheme.skyscraperResidueField x`, the skyscraper sheaf `κ(x)ₓ` as an `𝒪_X`-module;
* `Scheme.skyscraperResidueFieldEquiv`, the identification of its sections over an open subset
  containing `x` with `κ(x)`, under which a regular function acts by multiplication with its
  value at `x` (`Scheme.skyscraperResidueFieldEquiv_smul`), and which commutes with restriction
  (`Scheme.skyscraperResidueFieldEquiv_map`);
* `Scheme.subsingleton_skyscraperResidueField`: the sections over an open subset not containing
  `x` vanish;
* `Scheme.isFlasque_skyscraperResidueField`: the skyscraper sheaf is flasque, so its cohomology
  vanishes in positive degrees;
* `Scheme.finrank_cohomology_zero_skyscraperResidueField`: over a field `k`, the dimension of
  `H⁰(X, κ(x)ₓ)` is the residue degree `[κ(x) : k]` of the structure morphism at `x`, so that
  the cohomology is finite-dimensional when that degree is nonzero
  (`Scheme.finiteDimensional_cohomology_skyscraperResidueField`).

## References

* R. Hartshorne, *Algebraic Geometry*, II, Exercise 1.17 (skyscraper sheaves) and IV,
  Theorem 1.3 (their role in the proof of Riemann–Roch).

## Formalization notes

The pushforward construction, section equivalences, restriction-map arguments, and flasqueness
proof follow the implementation pattern in
`TauCeti/AlgebraicGeometry/Modules/RationalFunctions.lean`.
-/

public section

open CategoryTheory TopologicalSpace AlgebraicGeometry Opposite

namespace TauCeti

namespace AlgebraicGeometry

universe u

noncomputable section

open Scheme

variable {X : Scheme.{u}}

/-- The skyscraper sheaf `κ(x)ₓ` of the residue field at a point `x`, as an `𝒪_X`-module: the
pushforward of the structure sheaf of `Spec κ(x)` along `Scheme.fromSpecResidueField`. Its
sections are `κ(x)` over the open subsets containing `x` (`skyscraperResidueFieldEquiv`) and `0`
over the others (`subsingleton_skyscraperResidueField`). -/
def _root_.AlgebraicGeometry.Scheme.skyscraperResidueField (x : X) : X.Modules :=
  (Scheme.Modules.pushforward (X.fromSpecResidueField x)).obj (SheafOfModules.unit _)

private def residueFieldSectionsIso (x : X) {U : X.Opens} (hx : x ∈ U) :
    Γ(Spec (X.residueField x), X.fromSpecResidueField x ⁻¹ᵁ U) ≅ X.residueField x :=
  ((Spec (X.residueField x)).presheaf.mapIso
    (eqToIso (Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecResidueField x)
      (by
        convert hx using 1
        exact Scheme.fromSpecResidueField_apply x
          (IsLocalRing.closedPoint (X.residueField x))))).op).symm ≪≫
    Scheme.ΓSpecIso (X.residueField x)

/-- On an open subset containing `x`, the morphism `Spec κ(x) ⟶ X` acts on sections by
evaluation at `x`. -/
private lemma app_comp_residueFieldSectionsIso (x : X) {U : X.Opens} (hx : x ∈ U) :
    (X.fromSpecResidueField x).app U ≫ (residueFieldSectionsIso x hx).hom =
      X.evaluation U x hx := by
  simp only [residueFieldSectionsIso, Iso.trans_hom, Iso.symm_hom, Functor.mapIso_inv]
  rw [← Category.assoc, Scheme.Hom.app_eq_appLE, Scheme.Hom.appLE_map]
  -- `fromSpecResidueField` is the composite `Spec κ(x) ⟶ Spec 𝒪_{X,x} ⟶ X`. Its `appLE` is
  -- transported along that factorization by hand, since unfolding it inside the dependent
  -- `appLE` produces a term which is not type-correct at reducible transparency.
  have key : ∀ {f g : Spec (X.residueField x) ⟶ X} (_ : f = g) (e : ⊤ ≤ f ⁻¹ᵁ U)
      (e' : ⊤ ≤ g ⁻¹ᵁ U), f.appLE U ⊤ e = g.appLE U ⊤ e' := by
    rintro _ _ rfl _ _
    rfl
  have hf : X.fromSpecResidueField x = Spec.map (X.residue x) ≫ X.fromSpecStalk x := by
    simp only [Scheme.fromSpecResidueField]
  have e' : ⊤ ≤ (Spec.map (X.residue x) ≫ X.fromSpecStalk x) ⁻¹ᵁ U := by
    rw [← hf, Scheme.preimage_eq_top_of_closedPoint_mem (X.fromSpecResidueField x)
      (by
        convert hx using 1
        exact Scheme.fromSpecResidueField_apply x
          (IsLocalRing.closedPoint (X.residueField x)))]
  rw [key hf _ e', Scheme.Hom.comp_appLE, Scheme.fromSpecStalk_app hx]
  have htop : ∀ e'' : (⊤ : (Spec (X.residueField x)).Opens) ≤
      Spec.map (X.residue x) ⁻¹ᵁ X.fromSpecStalk x ⁻¹ᵁ U,
      (Spec (X.presheaf.stalk x)).presheaf.map (homOfLE le_top).op ≫
        (Spec.map (X.residue x)).appLE (X.fromSpecStalk x ⁻¹ᵁ U) ⊤ e'' =
      (Spec.map (X.residue x)).appTop := fun _ ↦ by
    rw [Scheme.Hom.map_appLE, Scheme.Hom.appTop, Scheme.Hom.app_eq_appLE]
    rfl
  simp only [Category.assoc]
  rw [reassoc_of% (htop e'), Scheme.ΓSpecIso_naturality, Iso.inv_hom_id_assoc]
  exact X.germ_residue x hx

/-- The sections of the skyscraper sheaf `κ(x)ₓ` over an open subset containing `x` are the
residue field `κ(x)`. -/
def _root_.AlgebraicGeometry.Scheme.skyscraperResidueFieldEquiv (x : X) {U : X.Opens} (hx : x ∈ U) :
    Γ(skyscraperResidueField x, U) ≃+ X.residueField x :=
  (residueFieldSectionsIso x hx).commRingCatIsoToRingEquiv.toAddEquiv

/-- A regular function acts on the sections of `κ(x)ₓ` by multiplication with its value at `x`. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.skyscraperResidueFieldEquiv_smul
    (x : X) {U : X.Opens} (hx : x ∈ U) (r : Γ(X, U))
    (s : Γ(skyscraperResidueField x, U)) :
    skyscraperResidueFieldEquiv x hx (r • s) =
      X.evaluation U x hx r * skyscraperResidueFieldEquiv x hx s := by
  -- The action of `Γ(X, U)` on the pushforward is multiplication after applying the map on
  -- sections; the module-sheaf section type is definitionally the corresponding ring of sections
  -- of `Spec κ(x)`, the form used by `app_comp_residueFieldSectionsIso`.
  have h : skyscraperResidueFieldEquiv x hx (r • s) =
      (residueFieldSectionsIso x hx).hom ((X.fromSpecResidueField x).app U r *
        (id s : Γ(Spec (X.residueField x), X.fromSpecResidueField x ⁻¹ᵁ U))) := rfl
  rw [h, map_mul, ← CategoryTheory.ConcreteCategory.comp_apply,
    app_comp_residueFieldSectionsIso]
  rfl

/-- The identifications of the sections of `κ(x)ₓ` with `κ(x)` commute with restriction. -/
@[simp]
lemma _root_.AlgebraicGeometry.Scheme.skyscraperResidueFieldEquiv_map
    (x : X) {U V : X.Opens} (i : U ⟶ V) (hx : x ∈ U)
    (s : Γ(skyscraperResidueField x, V)) :
    skyscraperResidueFieldEquiv x hx ((skyscraperResidueField x).presheaf.map i.op s) =
      skyscraperResidueFieldEquiv x (i.le hx) s := by
  dsimp only [skyscraperResidueField, Scheme.Modules.pushforward_obj_presheaf_map]
  -- `pushforward_obj_presheaf_map` identifies the restriction map, but its source remains the
  -- module-sheaf section carrier, while `residueFieldSectionsIso` uses the definitionally equal
  -- ring-sheaf section carrier. There is no bundled equivalence between those carriers, so this
  -- conversion is needed before composing the named restriction map with the section isomorphism.
  change (residueFieldSectionsIso x hx).hom
    ((Spec (X.residueField x)).presheaf.map
      ((Opens.map (X.fromSpecResidueField x).base).map i).op
        (id s : Γ(Spec (X.residueField x), X.fromSpecResidueField x ⁻¹ᵁ V))) =
          (residueFieldSectionsIso x (i.le hx)).hom s
  rw [← CategoryTheory.ConcreteCategory.comp_apply]
  congr 1

/-- The skyscraper sheaf `κ(x)ₓ` has no nonzero sections over an open subset not containing
`x`. -/
lemma _root_.AlgebraicGeometry.Scheme.subsingleton_skyscraperResidueField
    (x : X) {U : X.Opens} (hx : x ∉ U) :
    Subsingleton Γ(skyscraperResidueField x, U) := by
  have hpreimage : X.fromSpecResidueField x ⁻¹ᵁ U = ⊥ := by
    rw [← Opens.coe_eq_empty, Scheme.Hom.coe_preimage, Set.preimage_eq_empty_iff,
      Scheme.range_fromSpecResidueField,
      Set.disjoint_singleton_right]
    exact hx
  have : Subsingleton Γ(Spec (X.residueField x), X.fromSpecResidueField x ⁻¹ᵁ U) := by
    rw [hpreimage]
    infer_instance
  exact this

/-- The restriction maps of `κ(x)ₓ` between open subsets containing `x` are bijective. -/
lemma _root_.AlgebraicGeometry.Scheme.skyscraperResidueField_map_bijective
    (x : X) {U V : X.Opens} (i : U ⟶ V) (hx : x ∈ U) :
    Function.Bijective ((skyscraperResidueField x).presheaf.map i.op) := by
  have h : ⇑((skyscraperResidueField x).presheaf.map i.op) =
      (skyscraperResidueFieldEquiv x hx).symm ∘ skyscraperResidueFieldEquiv x (i.le hx) := by
    funext s
    rw [Function.comp_apply, ← skyscraperResidueFieldEquiv_map x i hx,
      AddEquiv.symm_apply_apply]
  rw [h]
  exact (skyscraperResidueFieldEquiv x hx).symm.bijective.comp
    (skyscraperResidueFieldEquiv x (i.le hx)).bijective

/-- The skyscraper sheaf `κ(x)ₓ` is flasque: its restriction maps are bijective between open
subsets containing `x`, and land in the zero group otherwise. -/
instance _root_.AlgebraicGeometry.Scheme.isFlasque_skyscraperResidueField (x : X) :
    (skyscraperResidueField x).presheaf.IsFlasque where
  epi {U V} i := by
    rw [AddCommGrpCat.epi_iff_surjective]
    by_cases hx : x ∈ V.unop
    · exact (skyscraperResidueField_map_bijective x i.unop hx).surjective
    · have := subsingleton_skyscraperResidueField x hx
      exact fun _ ↦ ⟨0, Subsingleton.elim _ _⟩

section Base

variable (k : Type u) [Field k] [X.Over (Spec (.of k))]

/-- **The dimension of the global sections of a skyscraper sheaf.** Over a field `k`, the zeroth
cohomology `H⁰(X, κ(x)ₓ) = κ(x)` has dimension the residue degree `[κ(x) : k]` of the structure
morphism at `x` (which is `0` by convention when `κ(x)` is infinite over `k`). -/
theorem _root_.AlgebraicGeometry.Scheme.finrank_cohomology_zero_skyscraperResidueField (x : X) :
    Module.finrank k (Scheme.Modules.Cohomology (skyscraperResidueField x) 0) =
      (X ↘ Spec (.of k)).residueDegree x := by
  let f := X ↘ Spec (.of k)
  let : Algebra ((Spec (.of k)).residueField (f x)) (X.residueField x) :=
    (f.residueFieldMap x).hom.toAlgebra
  rw [(Scheme.Modules.cohomologyZeroBaseLinearEquiv k X _).finrank_eq, Scheme.Hom.residueDegree,
    Module.finrank, Module.finrank]
  congr 1
  have hx : x ∈ (⊤ : X.Opens) := trivial
  refine rank_eq_of_equiv_equiv _ (skyscraperResidueFieldEquiv x hx)
    (Γevaluation_comp_ΓSpecIso_inv_bijective k (f x)) fun c s ↦ ?_
  rw [Scheme.Modules.base_smul_globalSections, skyscraperResidueFieldEquiv_smul,
    Algebra.smul_def, RingHom.algebraMap_toAlgebra, Function.comp_apply,
    Scheme.Γevaluation_naturality_apply, Scheme.Modules.baseRingToGlobalSections_apply]

/-- At a point whose residue field is finite over `k`, the skyscraper sheaf `κ(x)ₓ` has
finite-dimensional cohomology in every degree: `κ(x)` in degree zero and `0` above. -/
theorem _root_.AlgebraicGeometry.Scheme.finiteDimensional_cohomology_skyscraperResidueField {x : X}
    (hx : (X ↘ Spec (.of k)).residueDegree x ≠ 0) (i : ℕ) :
    FiniteDimensional k (Scheme.Modules.Cohomology (skyscraperResidueField x) i) := by
  cases i with
  | zero =>
    refine Module.finite_of_finrank_pos ?_
    rw [finrank_cohomology_zero_skyscraperResidueField]
    exact Nat.pos_of_ne_zero hx
  | succ i => infer_instance

end Base

end

end AlgebraicGeometry

end TauCeti
