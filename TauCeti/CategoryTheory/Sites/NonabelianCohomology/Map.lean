/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Connecting
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.ContractedProduct

/-!
# Functoriality of torsor classes in the sheaf of groups

Let `φ : G ⟶ G'` be a morphism of sheaves of groups on a site `(C, J)`. Extending the structure
group of a `G`-torsor `P` along `φ` gives the `G'`-torsor `Torsor.map φ P`, the contracted
product `P ×^G G'` (see `NonabelianCohomology.ContractedProduct`). This file shows that it
induces a map `H¹(G) → H¹(G')` of pointed sets, functorial in `φ` and compatible with connecting
maps.

## Main declarations

* `CategoryTheory.Sheaf.NonabelianH1.map φ`: the induced map `H¹(G) → H¹(G')`, with
  `NonabelianH1.map_id`, `NonabelianH1.map_comp` and `NonabelianH1.map_one`.
* `CategoryTheory.Sheaf.NonabelianH1.map_mk_eq_mk`: a `φ`-equivariant morphism from `P` to a
  `G'`-torsor `R` identifies the image of the class of `P` with the class of `R`.
* `CategoryTheory.Sheaf.NonabelianH1.map_mk_eq_mk_iff`: the image of the class of `P` is the
  class of a `G'`-torsor `R` if and only if there is a `φ`-equivariant morphism from `P` to `R`.
* `CategoryTheory.Sheaf.NonabelianH1.map_connecting`: for an extension `1 → A → B → Q → 1`, the
  composite `Q(C) → H¹(A) → H¹(B)` is trivial.

## References

* [The Stacks project, Section 21.4 (03AG)](https://stacks.math.columbia.edu/tag/03AG).
* J. Giraud, *Cohomologie non abélienne*, Chapitre III, §1.3, for the contracted product of a
  torsor along a morphism of sheaves of groups.
-/

public noncomputable section

open CategoryTheory Opposite

universe w v u

namespace CategoryTheory.Sheaf

variable {C : Type u} [Category.{v} C] {J : GrothendieckTopology C}
  {G G' G'' : Sheaf J GrpCat.{w}}

namespace NonabelianH1

variable [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

/-- The map `H¹(G) → H¹(G')` induced by a morphism `φ : G ⟶ G'` of sheaves of groups, sending
the class of a `G`-torsor `P` to the class of the contracted product `P ×^G G'`. -/
def map (φ : G ⟶ G') : NonabelianH1 G → NonabelianH1 G' :=
  lift (fun P ↦ mk (P.map φ)) fun P Q f ↦ mk_eq_mk_of_hom <| P.mapLift (f.hom ≫ Q.toMap φ)
    fun U g p ↦ by simp [f.map_smul, Torsor.toMap_smul]

/-- `map φ` sends the class of `P` to the class of the contracted product `P ×^G G'`. -/
@[simp]
lemma map_mk (φ : G ⟶ G') (P : Torsor G) : map φ (mk P) = mk (P.map φ) :=
  lift_mk _ _ P

/-- A `φ`-equivariant morphism from a `G`-torsor `P` to a `G'`-torsor `R` identifies the image
of the class of `P` under `map φ` with the class of `R`. -/
lemma map_mk_eq_mk {φ : G ⟶ G'} {P : Torsor G} {R : Torsor G'} (u : P.sheaf ⟶ R.sheaf)
    (hu : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U),
      u.hom.app U (g • p) = φ.hom.app U g • u.hom.app U p) :
    map φ (mk P) = mk R :=
  (map_mk φ P).trans (mk_eq_mk_of_hom (P.mapLift u hu))

/-- The image of the class of a `G`-torsor `P` under `map φ` is the class of a `G'`-torsor `R` if
and only if there is a `φ`-equivariant morphism from `P` to `R`. -/
lemma map_mk_eq_mk_iff {φ : G ⟶ G'} {P : Torsor G} {R : Torsor G'} :
    map φ (mk P) = mk R ↔ ∃ u : P.sheaf ⟶ R.sheaf, ∀ (U : Cᵒᵖ) (g : G.obj.obj U)
      (p : P.sheaf.obj.obj U), u.hom.app U (g • p) = φ.hom.app U g • u.hom.app U p := by
  refine ⟨fun h ↦ ?_, fun ⟨u, hu⟩ ↦ map_mk_eq_mk u hu⟩
  obtain ⟨e⟩ := mk_eq_mk_iff.1 ((map_mk φ P).symm.trans h)
  exact ⟨P.toMap φ ≫ e.hom.hom, fun U g p ↦ by simp [Torsor.toMap_smul, e.hom.map_smul]⟩

/-- The identity of `G` induces the identity of `H¹(G)`. -/
@[simp]
lemma map_id : map (𝟙 G) = id := by
  funext x
  induction x using ind with | h P => ?_
  exact map_mk_eq_mk (𝟙 P.sheaf) fun _ _ _ ↦ rfl

/-- The maps induced on `H¹` by `φ` and `ψ` compose to the map induced by `φ ≫ ψ`. -/
@[simp]
lemma map_map (φ : G ⟶ G') (ψ : G' ⟶ G'') (x : NonabelianH1 G) :
    map ψ (map φ x) = map (φ ≫ ψ) x := by
  induction x using ind with | h P => ?_
  rw [map_mk, map_mk, map_mk]
  refine (mk_eq_mk_of_hom (P.mapLift (P.toMap φ ≫ (P.map φ).toMap ψ) fun U g p ↦ ?_)).symm
  simp [Torsor.toMap_smul]

/-- The map induced on `H¹` by a composite is the composite of the induced maps. -/
lemma map_comp (φ : G ⟶ G') (ψ : G' ⟶ G'') : map (φ ≫ ψ) = map ψ ∘ map φ :=
  funext fun x ↦ (map_map φ ψ x).symm

/-- `map φ` is a map of pointed sets: it sends the class of the trivial torsor to the class of
the trivial torsor. -/
@[simp]
lemma map_one (φ : G ⟶ G') : map φ 1 = 1 :=
  map_mk_eq_mk ((sheafCompose J (forget GrpCat.{w})).map φ) fun U g p ↦
    map_mul (φ.hom.app U).hom g p

/-- A morphism of sheaves of groups which is trivial on sections induces the constant map to the
base point. -/
lemma map_eq_one_of_forall_app_eq_one {φ : G ⟶ G'}
    (hφ : ∀ (U : Cᵒᵖ) (g : G.obj.obj U), φ.hom.app U g = 1) (x : NonabelianH1 G) :
    map φ x = 1 := by
  induction x using ind with | h P => ?_
  exact map_mk_eq_mk (R := Torsor.trivial G') (ObjectProperty.homMk
    { app U := ↾fun _ ↦ (1 : G'.obj.obj U)
      naturality U V f := by
        ext
        exact (_root_.map_one (G'.obj.map f).hom).symm })
    -- The action of `G'` on the trivial torsor is multiplication.
    fun U g _ ↦ (by rw [hφ, mul_one] : (1 : G'.obj.obj U) = φ.hom.app U g * 1)

/-- The connecting map is natural in a morphism of group extensions: extending the structure
group of the torsor of lifts along the map `α` of kernels gives the torsor of lifts of the
image section. The middle and quotient maps need not be injective or surjective. -/
theorem map_connecting_of_comp_eq {A B Q A' B' Q' : Sheaf J GrpCat.{w}}
    {i : A ⟶ B} {π : B ⟶ Q} {i' : A' ⟶ B'} {π' : B' ⟶ Q'}
    (hE : IsGroupExtension i π) (hE' : IsGroupExtension i' π')
    (α : A ⟶ A') (β : B ⟶ B') (γ : Q ⟶ Q')
    (hα : i ≫ β = α ≫ i') (hγ : β ≫ π' = π ≫ γ)
    (q : (Q.obj ⋙ forget GrpCat).sections) (q' : (Q'.obj ⋙ forget GrpCat).sections)
    (hq : ∀ U, γ.hom.app U (q.val U) = q'.val U) :
    map α (connecting hE q) = connecting hE' q' := by
  rw [connecting_def, connecting_def]
  exact map_mk_eq_mk (hE.liftsMap q hE' β γ hγ q' hq)
    (hE.liftsMap_smul q hE' β γ hγ q' hq α hα)

/-- For an extension `1 → A → B → Q → 1` of sheaves of groups, the composite
`Q(C) → H¹(A) → H¹(B)` is trivial: the torsor of lifts of a global section of `Q` maps to the
trivial `B`-torsor by the inclusion of lifts into `B`. -/
lemma map_connecting {A B Q : Sheaf J GrpCat.{w}} {i : A ⟶ B} {π : B ⟶ Q}
    (hE : IsGroupExtension i π) (q : (Q.obj ⋙ forget GrpCat).sections) :
    map i (connecting hE q) = 1 := by
  rw [connecting_def, ← mk_trivial]
  exact map_mk_eq_mk (R := Torsor.trivial B) (ObjectProperty.homMk
    { app U := ↾fun b ↦ (hE.liftsObjEquiv q U b).val
      naturality U V f := by
        ext b
        exact hE.liftsObjEquiv_map q f b })
    fun U a b ↦ hE.liftsObjEquiv_smul q a b

end NonabelianH1

end CategoryTheory.Sheaf
