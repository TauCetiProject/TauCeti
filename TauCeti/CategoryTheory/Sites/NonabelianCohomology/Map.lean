/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.Connecting
public import TauCeti.CategoryTheory.Sites.NonabelianCohomology.PreTorsor

/-!
# Functoriality of torsor classes in the sheaf of groups

Let `φ : G ⟶ G'` be a morphism of sheaves of groups on a site `(C, J)` and `P` a `G`-torsor.
The *contracted product* `P ×^G G'` is the sheafification of the presheaf
`U ↦ (P(U) × G'(U)) / G(U)`, where `g` sends `(p, a)` to `(g • p, a * φ(g)⁻¹)`, with `G'` acting
by left multiplication on the second factor. It is a `G'`-torsor, and `p ↦ [p, 1]` is a
`φ`-equivariant morphism `P → P ×^G G'` which is universal among `φ`-equivariant morphisms from
`P` to `G'`-torsors. This gives the map `H¹(G) → H¹(G')` of pointed sets.

## Main declarations

* `CategoryTheory.Sheaf.Torsor.map φ P`: the contracted product `P ×^G G'`.
* `CategoryTheory.Sheaf.Torsor.toMap φ P`: the `φ`-equivariant morphism `P → P ×^G G'`.
* `CategoryTheory.Sheaf.Torsor.mapLift`: a `φ`-equivariant morphism `P → R` to a `G'`-torsor
  induces a morphism of `G'`-torsors `P ×^G G' ⟶ R`; `Torsor.map_hom_ext` is its uniqueness.
* `CategoryTheory.Sheaf.NonabelianH1.map φ`: the induced map `H¹(G) → H¹(G')`, with
  `NonabelianH1.map_id`, `NonabelianH1.map_comp` and `NonabelianH1.map_one`.
* `CategoryTheory.Sheaf.NonabelianH1.map_mk_eq_mk`: a `φ`-equivariant morphism from `P` to a
  `G'`-torsor `R` identifies the image of the class of `P` with the class of `R`.
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

namespace Torsor

variable (φ : G ⟶ G') (P : Torsor G)

/-- The relation on `P(U) × G'(U)` generating the contracted product: `(p, a)` is related to
`(g • p, a * φ(g)⁻¹)`. -/
private def ContractedRel (U : Cᵒᵖ) (x y : P.sheaf.obj.obj U × G'.obj.obj U) : Prop :=
  ∃ g : G.obj.obj U, y = (g • x.1, x.2 * (φ.hom.app U g)⁻¹)

/-- The presheaf `U ↦ (P(U) × G'(U)) / G(U)` whose sheafification is the contracted product. -/
private def contractedPresheaf : Cᵒᵖ ⥤ Type w where
  obj U := Quot (ContractedRel φ P U)
  map {U V} f := ↾Quot.map (fun x ↦ (P.sheaf.obj.map f x.1, G'.obj.map f x.2)) (by
    rintro x _ ⟨g, rfl⟩
    refine ⟨G.obj.map f g, Prod.ext (P.map_smul f g x.1) ?_⟩
    simp [NatTrans.naturality_apply φ.hom f g])
  map_id U := by
    ext y
    induction y using Quot.ind
    exact congrArg (Quot.mk _) (Prod.ext (by simp) (by simp))
  map_comp f g := by
    ext y
    induction y using Quot.ind
    exact congrArg (Quot.mk _) (Prod.ext (by simp) (by simp))

/-- Every element of the contracted product over `U` is the class of `(p₀, a)` for a given
section `p₀` of `P` over `U`. -/
private lemma exists_mk_eq {U : Cᵒᵖ} (p₀ : P.sheaf.obj.obj U) (y : Quot (ContractedRel φ P U)) :
    ∃ a, Quot.mk _ (p₀, a) = y := by
  induction y using Quot.ind with | mk x => ?_
  obtain ⟨d, hd⟩ := MulAction.exists_smul_eq (G.obj.obj U) p₀ x.1
  exact ⟨x.2 * φ.hom.app U d, Quot.sound ⟨d, Prod.ext hd.symm (by simp)⟩⟩

/-- The classes of `(p₀, a)` and `(p₀, b)` agree only if `a = b`, because `G` acts freely
on `P`. -/
private lemma mk_injective {U : Cᵒᵖ} (p₀ : P.sheaf.obj.obj U) {a b : G'.obj.obj U}
    (h : (Quot.mk _ (p₀, a) : Quot (ContractedRel φ P U)) = Quot.mk _ (p₀, b)) : a = b := by
  -- The class of `(p, c)` determines `c * φ(g)` for the `g` with `g • p₀ = p`.
  let inv : Quot (ContractedRel φ P U) → Prop :=
    Quot.lift (fun x ↦ ∃ g : G.obj.obj U, g • p₀ = x.1 ∧ x.2 * φ.hom.app U g = b) (by
      rintro x _ ⟨h, rfl⟩
      refine propext ⟨fun ⟨g, hg, hgb⟩ ↦ ⟨h * g, by rw [mul_smul, hg], ?_⟩,
        fun ⟨g, hg, hgb⟩ ↦ ⟨h⁻¹ * g, by rw [mul_smul, hg, inv_smul_smul], ?_⟩⟩
      · simpa [mul_assoc] using hgb
      · simpa [mul_assoc] using hgb)
  obtain ⟨g, hg, hgb⟩ : inv (Quot.mk _ (p₀, a)) := h ▸ ⟨1, one_smul _ _, by simp⟩
  obtain rfl : g = 1 := P.smul_left_injective p₀ (hg.trans (one_smul _ _).symm)
  simpa using hgb

/-- The contracted product before sheafification, a `G'`-pretorsor. -/
private def contracted : PreTorsor G' where
  presheaf := contractedPresheaf φ P
  mulAction U :=
    { smul a := Quot.map (fun x ↦ (x.1, a * x.2)) (by
        rintro x _ ⟨g, rfl⟩
        exact ⟨g, Prod.ext rfl (mul_assoc _ _ _).symm⟩)
      one_smul y := by
        induction y using Quot.ind
        exact congrArg (Quot.mk _) (Prod.ext rfl (one_mul _))
      mul_smul a b y := by
        induction y using Quot.ind
        exact congrArg (Quot.mk _) (Prod.ext rfl (mul_assoc _ _ _)) }
  map_smul U V f a y := by
    induction y using Quot.ind
    exact congrArg (Quot.mk _) (Prod.ext rfl (map_mul _ _ _))
  coversTop X := J.superset_covering (by
    rintro Y a ⟨⟨V, ⟨p⟩⟩, ⟨b⟩⟩
    exact ⟨⟨V, ⟨Quot.mk _ (p, 1)⟩⟩, ⟨b⟩⟩) (P.coversTop X)
  bijective U := by
    refine ⟨fun ⟨a, y⟩ ⟨b, y'⟩ h ↦ ?_, fun ⟨z, y⟩ ↦ ?_⟩
    · obtain ⟨h₁, rfl⟩ := Prod.ext_iff.1 h
      induction y using Quot.ind with | mk x => ?_
      exact Prod.ext (mul_right_cancel (mk_injective φ P x.1 h₁)) rfl
    · induction y using Quot.ind with | mk x => ?_
      obtain ⟨c, rfl⟩ := exists_mk_eq φ P x.1 z
      exact ⟨(c * x.2⁻¹, Quot.mk _ x),
        Prod.ext (congrArg (Quot.mk _) (Prod.ext rfl (inv_mul_cancel_right c x.2))) rfl⟩

/-- The map `p ↦ [p, 1]` from `P` to the contracted product before sheafification. -/
private def toContracted : P.sheaf.obj ⟶ (contracted φ P).presheaf where
  app U := ↾fun p ↦ Quot.mk _ (p, 1)
  naturality U V f := by
    ext p
    exact congrArg (Quot.mk _) (Prod.ext rfl (map_one _).symm)

/-- The map `p ↦ [p, 1]` is `φ`-equivariant: the classes of `(g • p, 1)` and `(p, φ(g))`
agree. -/
private lemma toContracted_smul {U : Cᵒᵖ} (g : G.obj.obj U) (p : P.sheaf.obj.obj U) :
    (toContracted φ P).app U (g • p) = φ.hom.app U g • (toContracted φ P).app U p :=
  (Quot.sound ⟨g, Prod.ext rfl (by simp)⟩).symm

variable [HasWeakSheafify J (Type w)] [J.WEqualsLocallyBijective (Type w)]

/-- The contracted product `P ×^G G'` of a `G`-torsor `P` along a morphism `φ : G ⟶ G'` of
sheaves of groups: the `G'`-torsor obtained from `P` by extending its structure group along `φ`.
Use `toMap`, `toMap_smul`, `mapLift` and `map_hom_ext` rather than unfolding it. -/
def map : Torsor G' :=
  (contracted φ P).sheafify

/-- The morphism `P → P ×^G G'`, `p ↦ [p, 1]`. -/
def toMap : P.sheaf ⟶ (P.map φ).sheaf :=
  ObjectProperty.homMk (toContracted φ P ≫ (contracted φ P).toSheafify)

/-- The morphism `P → P ×^G G'` is `φ`-equivariant. -/
@[simp]
lemma toMap_smul {U : Cᵒᵖ} (g : G.obj.obj U) (p : P.sheaf.obj.obj U) :
    (P.toMap φ).hom.app U (g • p) = φ.hom.app U g • (P.toMap φ).hom.app U p :=
  (congrArg ((contracted φ P).toSheafify.app U) (toContracted_smul φ P g p)).trans
    ((contracted φ P).toSheafify_smul (φ.hom.app U g) _)

variable {φ P}

/-- Morphisms of `G'`-torsors out of `P ×^G G'` are determined by their composite with the
morphism `P → P ×^G G'`. -/
lemma map_hom_ext {R : Torsor G'} {f f' : P.map φ ⟶ R}
    (h : P.toMap φ ≫ f.hom = P.toMap φ ≫ f'.hom) : f = f' := by
  refine (contracted φ P).sheafify_hom_ext ?_
  ext U y
  induction y using Quot.ind with | mk x => ?_
  -- The class of `(p, a)` is `a • [p, 1]`, and `f`, `f'` agree on `[p, 1]`.
  have hx : (Quot.mk _ x : (contracted φ P).presheaf.obj U) =
      x.2 • (toContracted φ P).app U x.1 :=
    congrArg (Quot.mk _) (Prod.ext rfl (mul_one _).symm)
  have h' : f.hom.hom.app U ((P.toMap φ).hom.app U x.1) =
      f'.hom.hom.app U ((P.toMap φ).hom.app U x.1) :=
    congrArg (fun g ↦ g.hom.app U x.1) h
  have key (g : P.map φ ⟶ R) :
      ((contracted φ P).toSheafify ≫ g.hom.hom).app U (Quot.mk _ x) =
        x.2 • g.hom.hom.app U ((P.toMap φ).hom.app U x.1) :=
    (congrArg (g.hom.hom.app U) ((congrArg _ hx).trans
      ((contracted φ P).toSheafify_smul _ _))).trans (g.map_smul U _ _)
  exact (key f).trans ((congrArg _ h').trans (key f').symm)

/-- A `φ`-equivariant morphism `u : P → R` to a `G'`-torsor induces a morphism of `G'`-torsors
`P ×^G G' ⟶ R`, sending `[p, a]` to `a • u p`. -/
def mapLift {R : Torsor G'} (u : P.sheaf ⟶ R.sheaf)
    (hu : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U),
      u.hom.app U (g • p) = φ.hom.app U g • u.hom.app U p) :
    P.map φ ⟶ R :=
  (contracted φ P).sheafifyLift
    { app U := ↾Quot.lift (fun x ↦ x.2 • u.hom.app U x.1) (by
        rintro x _ ⟨g, rfl⟩
        dsimp
        rw [hu, mul_smul, inv_smul_smul])
      naturality U V f := by
        ext y
        induction y using Quot.ind with | mk x => ?_
        exact ((R.map_smul f x.2 (u.hom.app U x.1)).trans
          (congrArg _ (NatTrans.naturality_apply u.hom f x.1).symm)).symm }
    fun U a y ↦ by
      induction y using Quot.ind with | mk x => ?_
      exact mul_smul a x.2 (u.hom.app U x.1)

/-- The morphism induced by a `φ`-equivariant `u : P → R` restricts to `u` along
`P → P ×^G G'`. -/
@[reassoc (attr := simp)]
lemma toMap_mapLift {R : Torsor G'} (u : P.sheaf ⟶ R.sheaf)
    (hu : ∀ (U : Cᵒᵖ) (g : G.obj.obj U) (p : P.sheaf.obj.obj U),
      u.hom.app U (g • p) = φ.hom.app U g • u.hom.app U p) :
    P.toMap φ ≫ (P.mapLift u hu).hom = u := by
  ext U p
  exact ((contracted φ P).sheafifyLift_hom_app_toSheafify _ _ _).trans (one_smul _ _)

end Torsor

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

/-- For an extension `1 → A → B → Q → 1` of sheaves of groups, the composite
`Q(C) → H¹(A) → H¹(B)` is trivial: the torsor of lifts of a global section of `Q` maps to the
trivial `B`-torsor by the inclusion of lifts into `B`. -/
lemma map_connecting {A B Q : Sheaf J GrpCat.{w}} {i : A ⟶ B} {π : B ⟶ Q}
    (hE : IsGroupExtension i π) (q : (Q.obj ⋙ forget GrpCat).sections) :
    map i (connecting hE q) = 1 := by
  rw [connecting_def, ← mk_trivial]
  exact map_mk_eq_mk (R := Torsor.trivial B) (ObjectProperty.homMk
    { app U := ↾fun b ↦ (hE.liftsObjEquiv q U b).1
      naturality U V f := by
        ext b
        exact hE.liftsObjEquiv_map q f b })
    fun U a b ↦ hE.liftsObjEquiv_smul q a b

end NonabelianH1

end CategoryTheory.Sheaf
