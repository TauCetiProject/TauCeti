/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Claude
-/
module

public import Mathlib.RepresentationTheory.Coinduced
public import Mathlib.RepresentationTheory.FiniteIndex
public import TauCeti.GroupTheory.Coset.Basic
public import TauCeti.RepresentationTheory.Induction.Permutation
public import TauCeti.RepresentationTheory.Rep.OfMulAction

/-!
# Induction and coinduction from the trivial subgroup

For a group `G` and a `k`-module `X`, the representation coinduced from the trivial subgroup,
`coindBot k G X = Coind_⊥^G X`, is the module of functions `G → X` with `G` acting by right
translation, `(g • f) h = f (h * g)`, and the representation induced from the trivial subgroup,
`indBot k G X = Ind_⊥^G X`, is `k[G] ⊗ X`, which is the module of finitely supported functions
`G →₀ X` with the same right-translation action (`Rep.indBotEquivFinsupp`). Every representation
`A` embeds into `coindBot k G A.V` (by `a ↦ (g ↦ g • a)`) and is a quotient of `indBot k G A.V`;
these are the two maps used for dimension shifting. For a finite group the two constructions agree
(`Rep.indBotIsoCoindBot`), and for any group `k[G]` is induced from the trivial subgroup
(`Rep.indBotIsoLeftRegular`).

Both constructions are stable under restriction to a subgroup `S`: writing `G` as `S × G ⧸ S`
through `(s, y) ↦ y.out * s` (Mathlib's `Subgroup.groupEquivQuotientProdSubgroup`), the restriction
of `Coind_⊥^G X` to `S` is `Coind_⊥^S (G ⧸ S → X)` (`Rep.resCoindBotIso`), and
the restriction of `Ind_⊥^G X` to `S` is `Ind_⊥^S (G ⧸ S →₀ X)` (`Rep.resIndBotIso`).

The constructions follow `ClassFieldTheory/Cohomology/IndCoind/Finite.lean` and
`IndCoind/TrivialCohomology.lean` in `kbuzzard/ClassFieldTheory`, commit
`ccc3323c6750abca25b49b35106f54eb3a398509`, adapted to Mathlib's `Rep.coind` and `Rep.ind`.

## Main definitions

* `Rep.coindBot`, `Rep.coindBotFunctor`: coinduction from the trivial subgroup.
* `Rep.coindBotUnit`: the monomorphism `A ⟶ coindBot k G A.V`.
* `Rep.indBot`, `Rep.indBotFunctor`: induction from the trivial subgroup.
* `Rep.indBotCounit`: the epimorphism `indBot k G A.V ⟶ A`.
* `Rep.coindBotEquivPi`, `Rep.indBotEquivFinsupp`: the underlying modules as functions `G → X`
  and finitely supported functions `G →₀ X`.
* `Rep.indBotIsoCoindBot`: for a finite group, `indBot k G X ≅ coindBot k G X`.
* `Rep.indBotIsoLeftRegular`: `indBot k G k ≅ k[G]`.
* `Rep.leftRegularIsoCoindBot`: for a finite group, `k[G] ≅ coindBot k G k`.
* `Rep.resCoindBotIso`, `Rep.resIndBotIso`: restrictions to a subgroup, again coinduced,
  respectively induced, from the trivial subgroup.

## References

* J. S. Milne, *Class Field Theory*, Chapter II, §1.
* K. S. Brown, *Cohomology of Groups*, Chapter III, §5.
-/

public noncomputable section

universe u

open CategoryTheory Representation

namespace Rep

variable {k G : Type u} [CommRing k] [Group G]

/-- The restriction of a representation to the trivial subgroup is the trivial representation on
its underlying module. -/
def resBotIsoTrivial (A : Rep k G) :
    res (⊥ : Subgroup G).subtype A ≅ trivial k (⊥ : Subgroup G) A.V :=
  mkIso <| .mk (LinearEquiv.refl k A.V) fun s ↦ by
    obtain rfl : s = 1 := Subsingleton.elim s 1
    ext
    simp

/-- The identification of the restriction to the trivial subgroup with the trivial representation
does not move elements. -/
@[simp]
theorem resBotIsoTrivial_hom_hom_apply (A : Rep k G) (x : A.V) :
    (resBotIsoTrivial A).hom.hom x = x :=
  (rfl)

/-- The inverse identification of the trivial representation with the restriction to the trivial
subgroup does not move elements. -/
@[simp]
theorem resBotIsoTrivial_inv_hom_apply (A : Rep k G) (x : A.V) :
    (resBotIsoTrivial A).inv.hom x = x :=
  (rfl)

section Coinduction

variable (k G) in
/-- The representation of `G` coinduced from the trivial subgroup on a `k`-module `X`: the
functions `G → X`, with `G` acting by right translation, `(g • f) h = f (h * g)`. -/
abbrev coindBot (X : Type u) [AddCommGroup X] [Module k X] : Rep k G :=
  coind (⊥ : Subgroup G).subtype (trivial k (⊥ : Subgroup G) X)

-- Not `@[simp]`: simp first unfolds the action `(coindBot k G X).ρ g` through
-- `Representation.coind_apply`, so the left-hand side is not in simp-normal form (`simpNF`).
/-- `G` acts on the representation coinduced from the trivial subgroup by right translation. -/
theorem coindBot_ρ_apply_coe (X : Type u) [AddCommGroup X] [Module k X] (g : G)
    (f : coindBot k G X) (h : G) :
    (((coindBot k G X).ρ g) f).1 h = f.1 (h * g) :=
  (rfl)

variable (k G) in
/-- Coinduction from the trivial subgroup, as a functor `ModuleCat k ⥤ Rep k G`. -/
-- The body is exposed because the object and map characterizations below mention `coindBot`
-- elements of `(coindBotFunctor k G).obj X`; with an opaque body those statements do not
-- typecheck in the public view of this module.
@[expose] def coindBotFunctor : ModuleCat.{u} k ⥤ Rep k G :=
  trivialFunctor k (⊥ : Subgroup G) ⋙ coindFunctor k (⊥ : Subgroup G).subtype

/-- Evaluating the coinduction functor from the trivial subgroup gives `coindBot`. -/
@[simp]
theorem coindBotFunctor_obj (X : ModuleCat.{u} k) : (coindBotFunctor k G).obj X = coindBot k G X :=
  (rfl)

/-- The coinduction functor from the trivial subgroup acts on a morphism by postcomposition. -/
@[simp]
theorem coindBotFunctor_map_hom_apply_coe {X Y : ModuleCat.{u} k} (f : X ⟶ Y)
    (x : coindBot k G X) (g : G) :
    (((coindBotFunctor k G).map f).hom x).1 g = f.hom (x.1 g) :=
  (rfl)

/-- The canonical embedding of a representation `A` into the representation coinduced from the
trivial subgroup on its underlying module, `a ↦ (g ↦ A.ρ g a)`. -/
def coindBotUnit (A : Rep k G) : A ⟶ coindBot k G A.V :=
  resCoindToHom (⊥ : Subgroup G).subtype A (trivial k (⊥ : Subgroup G) A.V)
    (resBotIsoTrivial A).hom

/-- The embedding into the coinduced representation sends `a` to the function `g ↦ A.ρ g a`. -/
@[simp]
theorem coindBotUnit_hom_apply_coe (A : Rep k G) (a : A) (g : G) :
    ((coindBotUnit A).hom a).1 g = A.ρ g a :=
  (rfl)

/-- The embedding into the coinduced representation is a monomorphism. -/
instance coindBotUnit_mono (A : Rep k G) : Mono (coindBotUnit A) :=
  (mono_iff_injective _).2 fun x y h ↦ by
    have h1 : A.ρ 1 x = A.ρ 1 y := by
      rw [← coindBotUnit_hom_apply_coe, ← coindBotUnit_hom_apply_coe, h]
    simpa using h1

variable (k G) in
/-- The underlying module of the representation coinduced from the trivial subgroup is the module
of all functions `G → X`. -/
def coindBotEquivPi (X : Type u) [AddCommGroup X] [Module k X] :
    (coindBot k G X : Type u) ≃ₗ[k] (G → X) where
  toFun f := f.1
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  invFun f := ⟨f, fun g h ↦ by
    obtain rfl : g = 1 := Subsingleton.elim g 1
    simp⟩
  left_inv _ := rfl
  right_inv _ := rfl

/-- The identification of the coinduced module with functions is the underlying function. -/
@[simp]
theorem coindBotEquivPi_apply (X : Type u) [AddCommGroup X] [Module k X] (f : coindBot k G X) :
    coindBotEquivPi k G X f = f.1 :=
  (rfl)

/-- The inverse identification of functions with the coinduced module is the underlying
function. -/
@[simp]
theorem coindBotEquivPi_symm_apply_coe (X : Type u) [AddCommGroup X] [Module k X] (f : G → X) :
    ((coindBotEquivPi k G X).symm f).1 = f :=
  (rfl)

end Coinduction

section Induction

-- `Finsupp` and the tensor-product identifications of `indBotEquivFinsupp` need decidable
-- equality of the group; nothing in the statements below depends on the choice.
attribute [local instance] Classical.decEq

variable (k G) in
/-- The representation of `G` induced from the trivial subgroup on a `k`-module `X`, namely
`k[G] ⊗[k] X` with `G` acting on `k[G]`. -/
abbrev indBot (X : Type u) [AddCommGroup X] [Module k X] : Rep k G :=
  ind (⊥ : Subgroup G).subtype (trivial k (⊥ : Subgroup G) X)

variable (k G) in
/-- Induction from the trivial subgroup, as a functor `ModuleCat k ⥤ Rep k G`. -/
-- The body is exposed for the same reason as `coindBotFunctor`: `indBotFunctor_map_hom_mk`
-- evaluates the map on generators of `(indBotFunctor k G).obj X`.
@[expose] def indBotFunctor : ModuleCat.{u} k ⥤ Rep k G :=
  trivialFunctor k (⊥ : Subgroup G) ⋙ indFunctor k (⊥ : Subgroup G).subtype

/-- Evaluating the induction functor from the trivial subgroup gives `indBot`. -/
@[simp]
theorem indBotFunctor_obj (X : ModuleCat.{u} k) : (indBotFunctor k G).obj X = indBot k G X :=
  (rfl)

-- The generator-evaluation lemmas below are not simp lemmas: their `IndV.mk` arguments unfold
-- under simp, so `@[simp]` would violate the `simpNF` linter.
/-- The induction functor from the trivial subgroup acts on generators through the morphism:
`⟦g ⊗ₜ x⟧ ↦ ⟦g ⊗ₜ f x⟧`. -/
theorem indBotFunctor_map_hom_mk {X Y : ModuleCat.{u} k} (f : X ⟶ Y) (g : G) (x : X) :
    ((indBotFunctor k G).map f).hom
        (IndV.mk (⊥ : Subgroup G).subtype (Representation.trivial k (⊥ : Subgroup G) X) g x) =
      IndV.mk (⊥ : Subgroup G).subtype (Representation.trivial k (⊥ : Subgroup G) Y) g (f.hom x) :=
  (rfl)

/-- The canonical projection from the representation induced from the trivial subgroup on the
underlying module of `A` onto `A`, `⟦g ⊗ₜ a⟧ ↦ A.ρ g⁻¹ a`. -/
def indBotCounit (A : Rep k G) : indBot k G A.V ⟶ A :=
  (indResHomEquiv (⊥ : Subgroup G).subtype (trivial k (⊥ : Subgroup G) A.V) A).symm
    (resBotIsoTrivial A).inv

/-- The projection from the induced representation on generators: `⟦g ⊗ₜ a⟧ ↦ A.ρ g⁻¹ a`. -/
theorem indBotCounit_hom_mk (A : Rep k G) (g : G) (a : A) :
    (indBotCounit A).hom
        (IndV.mk (⊥ : Subgroup G).subtype (Representation.trivial k (⊥ : Subgroup G) A.V) g a) =
      A.ρ g⁻¹ a := by
  simp [indBotCounit, resBotIsoTrivial]

/-- The projection from the induced representation is an epimorphism. -/
instance indBotCounit_epi (A : Rep k G) : Epi (indBotCounit A) :=
  (epi_iff_surjective _).2 fun a ↦ ⟨IndV.mk _ _ 1 a, by rw [indBotCounit_hom_mk, inv_one, map_one,
    Module.End.one_apply]⟩

variable (k G) in
/-- The underlying module of the representation induced from the trivial subgroup is the module
of finitely supported functions `G →₀ X`, `⟦g ⊗ₜ x⟧ ↦ single g x`: the coinvariants of the trivial
group are the whole module `k[G] ⊗ X`. -/
def indBotEquivFinsupp (X : Type u) [AddCommGroup X] [Module k X] :
    (indBot k G X : Type u) ≃ₗ[k] (G →₀ X) :=
  LinearEquiv.ofLinearMap
    (Coinvariants.lift _ (TensorProduct.finsuppScalarLeft k X G ∘ₗ
        (MonoidAlgebra.coeffLinearEquiv k).toLinearMap.rTensor X) fun g ↦ by
      obtain rfl : g = 1 := Subsingleton.elim g 1
      rw [map_one, Module.End.one_eq_id, LinearMap.comp_id])
    (Coinvariants.mk _ ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).symm.toLinearMap.rTensor X ∘ₗ
      (TensorProduct.finsuppScalarLeft k X G).symm.toLinearMap)
    (Finsupp.lhom_ext fun g x ↦ by simp [TensorProduct.finsuppScalarLeft_apply_tmul])
    (IndV.hom_ext _ _ fun g ↦ LinearMap.ext fun x ↦ by
      simp [TensorProduct.finsuppScalarLeft_apply_tmul])

/-- The underlying module of the induced representation on generators: `⟦g ⊗ₜ x⟧ ↦ single g x`. -/
theorem indBotEquivFinsupp_mk (X : Type u) [AddCommGroup X] [Module k X] (g : G) (x : X) :
    indBotEquivFinsupp k G X
        (IndV.mk (⊥ : Subgroup G).subtype (Representation.trivial k (⊥ : Subgroup G) X) g x) =
      Finsupp.single g x := by
  simp [indBotEquivFinsupp, TensorProduct.finsuppScalarLeft_apply_tmul]

/-- `G` acts on the finitely supported functions underlying the representation induced from the
trivial subgroup by right translation: `(g • v) h = v (h * g)`. -/
-- Not `@[simp]`: simp first unfolds the action `(indBot k G X).ρ g` through
-- `Representation.ind_apply`, so the left-hand side is not in simp-normal form (`simpNF`).
theorem indBotEquivFinsupp_ρ_apply (X : Type u) [AddCommGroup X] [Module k X] (g : G)
    (v : indBot k G X) (h : G) :
    indBotEquivFinsupp k G X ((indBot k G X).ρ g v) h = indBotEquivFinsupp k G X v (h * g) := by
  refine LinearMap.congr_fun (f := Finsupp.lapply h ∘ₗ (indBotEquivFinsupp k G X).toLinearMap ∘ₗ
      (indBot k G X).ρ g) (g := Finsupp.lapply (h * g) ∘ₗ (indBotEquivFinsupp k G X).toLinearMap)
    (IndV.hom_ext _ _ fun h' ↦ LinearMap.ext fun x ↦ ?_) v
  -- On the generator `⟦h' ⊗ₜ x⟧` both sides are values of single functions. The goal is restated
  -- with the generator folded: `IndV.mk` is a reducible abbreviation for a composite of linear
  -- maps, so `simp`/`rw [LinearMap.comp_apply]` unfold it into
  -- `Coinvariants.mk (single h' 1 ⊗ₜ x)`, where `Representation.ind_mk` and
  -- `indBotEquivFinsupp_mk` (stated on `IndV.mk`) no longer match.
  change indBotEquivFinsupp k G X (Representation.ind _ _ g
      (IndV.mk (⊥ : Subgroup G).subtype (Representation.trivial k (⊥ : Subgroup G) X) h' x)) h =
    indBotEquivFinsupp k G X
      (IndV.mk (⊥ : Subgroup G).subtype (Representation.trivial k (⊥ : Subgroup G) X) h' x) (h * g)
  rw [Representation.ind_mk, indBotEquivFinsupp_mk, indBotEquivFinsupp_mk, Finsupp.single_apply,
    Finsupp.single_apply]
  simp only [mul_inv_eq_iff_eq_mul]

/-- For any group, `k[G]` is induced from the trivial subgroup: `Ind_⊥^G k ≅ k[G ⧸ ⊥] ≅ k[G]`. -/
def indBotIsoLeftRegular : indBot k G k ≅ leftRegular k G :=
  TauCeti.indTrivialIso k (⊥ : Subgroup G) ≪≫ TauCeti.quotientBotIsoLeftRegular k

/-- The isomorphism from induction out of the trivial subgroup to the left regular
representation reads the underlying finitely supported function with inverted indices. -/
@[simp]
theorem indBotIsoLeftRegular_hom_hom_apply_coeff (v : indBot k G k) (g : G) :
    ((indBotIsoLeftRegular : indBot k G k ≅ leftRegular k G).hom.hom v).coeff g =
      indBotEquivFinsupp k G k v g⁻¹ := by
  refine LinearMap.congr_fun
    (f := Finsupp.lapply g ∘ₗ (MonoidAlgebra.coeffLinearEquiv k).toLinearMap ∘ₗ
      (indBotIsoLeftRegular : indBot k G k ≅ leftRegular k G).hom.hom.toLinearMap)
    (g := Finsupp.lapply g⁻¹ ∘ₗ (indBotEquivFinsupp k G k).toLinearMap)
    (IndV.hom_ext _ _ fun h ↦ LinearMap.ext fun a ↦ ?_) v
  change ((indBotIsoLeftRegular : indBot k G k ≅ leftRegular k G).hom.hom
      (IndV.mk (⊥ : Subgroup G).subtype (Representation.trivial k (⊥ : Subgroup G) k) h a)).coeff
    g = indBotEquivFinsupp k G k
      (IndV.mk (⊥ : Subgroup G).subtype (Representation.trivial k (⊥ : Subgroup G) k) h a) g⁻¹
  simp only [indBotIsoLeftRegular, Iso.trans_hom, hom_comp,
    IntertwiningMap.comp_apply]
  rw [TauCeti.indTrivialIso, Rep.mkIso_hom_hom_apply,
    Representation.Equiv.coe_toLinearMap,
    TauCeti.indTrivialEquiv_apply_mk,
    TauCeti.quotientBotIsoLeftRegular_hom_hom_single_mk,
    indBotEquivFinsupp_mk]
  simp only [MonoidAlgebra.coeff_single, Finsupp.single_apply]
  by_cases hg : h⁻¹ = g
  · have hg' : h = g⁻¹ := inv_eq_iff_eq_inv.mp hg
    simp [hg']
  · have hg' : h ≠ g⁻¹ := fun e ↦ hg (inv_eq_iff_eq_inv.mpr e)
    simp [hg, hg']

end Induction

section Finite

variable [Finite G]

-- Mathlib's `indCoindIso` is stated with a decidability hypothesis on the right coset relation;
-- for the trivial subgroup we supply it classically.
attribute [local instance] Classical.decRel

/-- For a finite group, induction and coinduction from the trivial subgroup agree. -/
def indBotIsoCoindBot (X : Type u) [AddCommGroup X] [Module k X] : indBot k G X ≅ coindBot k G X :=
  indCoindIso (trivial k (⊥ : Subgroup G) X)

/-- For a finite group, the left regular representation `k[G]` is coinduced from the trivial
subgroup. -/
def leftRegularIsoCoindBot : leftRegular k G ≅ coindBot k G k :=
  indBotIsoLeftRegular.symm ≪≫ indBotIsoCoindBot k

end Finite

section Restriction

variable (S : Subgroup G)

/-- The restriction to a subgroup `S` of a representation coinduced from the trivial subgroup of
`G` is coinduced from the trivial subgroup of `S`, on `[G : S]` copies of the coefficients:
`f ↦ (s ↦ (y ↦ f (y.out * s)))` (`resCoindBotIso_hom_hom_apply_coe`). -/
def resCoindBotIso (X : Type u) [AddCommGroup X] [Module k X] :
    res S.subtype (coindBot k G X) ≅ coindBot k S (G ⧸ S → X) :=
  mkIso <| .mk (coindBotEquivPi k G X ≪≫ₗ
    LinearEquiv.funCongrLeft k X
      ((Equiv.prodComm S (G ⧸ S)).trans Subgroup.groupEquivQuotientProdSubgroup.symm) ≪≫ₗ
    LinearEquiv.curry k X S (G ⧸ S) ≪≫ₗ (coindBotEquivPi k S (G ⧸ S → X)).symm) fun s ↦ by
    ext f h y
    -- Both sides evaluate `f` at a point of `G`, written through the coset decomposition of `G`.
    -- The goal is restated because the action of `s` on `res S.subtype (coindBot k G X)` is the
    -- `Representation.coind` operator applied through `LinearMap.funLeft`/`restrict`, and the
    -- forward map is a composite of `LinearEquiv.funCongrLeft` and `LinearEquiv.curry`: `simp`
    -- normalizes these into `Function.curry`/`funLeft` forms in which the argument
    -- `groupEquivQuotientProdSubgroup.symm (y, h)` is no longer exposed for its evaluation lemma.
    change f.1 (Subgroup.groupEquivQuotientProdSubgroup.symm (y, h) * s) =
      f.1 (Subgroup.groupEquivQuotientProdSubgroup.symm (y, h * s))
    rw [Subgroup.groupEquivQuotientProdSubgroup_symm_apply,
      Subgroup.groupEquivQuotientProdSubgroup_symm_apply, Subgroup.coe_mul, mul_assoc]

/-- The restriction of a coinduced representation to `S`: `f ↦ (s ↦ (y ↦ f (y.out * s)))`. -/
@[simp]
theorem resCoindBotIso_hom_hom_apply_coe (X : Type u) [AddCommGroup X] [Module k X]
    (f : coindBot k G X) (s : S) (y : G ⧸ S) :
    (((resCoindBotIso S X).hom.hom f).1 s) y = f.1 (y.out * s) :=
  -- The forward map evaluates `f` at the point of `G` with coset `y` and subgroup part `s`.
  congrArg f.1 (Subgroup.groupEquivQuotientProdSubgroup_symm_apply y s)

/-- The inverse of the restriction of a coinduced representation to `S`: a function
`F : S → (G ⧸ S → X)` goes to `g ↦ F (⟦g⟧.out⁻¹ * g) ⟦g⟧`, read through Mathlib's decomposition
`Subgroup.groupEquivQuotientProdSubgroup` of `g`. -/
@[simp]
theorem resCoindBotIso_inv_hom_apply_coe (X : Type u) [AddCommGroup X] [Module k X]
    (F : coindBot k S (G ⧸ S → X)) (g : G) :
    ((resCoindBotIso S X).inv.hom F).1 g =
      F.1 (Subgroup.groupEquivQuotientProdSubgroup g).2
        (Subgroup.groupEquivQuotientProdSubgroup g).1 :=
  (rfl)

/-- The restriction to a subgroup `S` of a representation induced from the trivial subgroup of `G`
is induced from the trivial subgroup of `S`, on the finitely supported functions `G ⧸ S →₀ X`: a
finitely supported function on `G = S × G ⧸ S` is a finitely supported function on `S` with values
finitely supported on `G ⧸ S` (`indBotEquivFinsupp_resIndBotIso_hom_hom_apply`). -/
def resIndBotIso (X : Type u) [AddCommGroup X] [Module k X] :
    res S.subtype (indBot k G X) ≅ indBot k S (G ⧸ S →₀ X) :=
  mkIso <| .mk (indBotEquivFinsupp k G X ≪≫ₗ
    Finsupp.domLCongr (Subgroup.groupEquivQuotientProdSubgroup.trans (Equiv.prodComm (G ⧸ S) S)) ≪≫ₗ
    Finsupp.curryLinearEquiv k ≪≫ₗ (indBotEquivFinsupp k S (G ⧸ S →₀ X)).symm) fun s ↦
    LinearMap.ext fun v ↦ (indBotEquivFinsupp k S (G ⧸ S →₀ X)).injective <|
      Finsupp.ext fun t ↦ Finsupp.ext fun y ↦ by
        -- Both sides evaluate the finitely supported function of `v` at a point of `G`, written
        -- through the coset decomposition of `G`; the action of `s` is right translation.
        rw [LinearMap.comp_apply, LinearMap.comp_apply, MonoidHom.comp_apply, Subgroup.coe_subtype,
          indBotEquivFinsupp_ρ_apply]
        simp only [LinearEquiv.coe_coe, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply,
          Finsupp.domLCongr_apply, Finsupp.domCongr_apply, Finsupp.curryLinearEquiv_apply,
          Finsupp.curry_apply, Finsupp.equivMapDomain_apply, Equiv.symm_trans_apply,
          Equiv.prodComm_symm, Equiv.prodComm_apply, Prod.swap_prod_mk,
          Subgroup.groupEquivQuotientProdSubgroup_symm_apply]
        rw [indBotEquivFinsupp_ρ_apply, Subgroup.coe_mul, mul_assoc]

/-- The restriction of an induced representation to `S`: the finitely supported function attached
to `v` sends `s` to the finitely supported function `y ↦ v (y.out * s)`. -/
@[simp]
theorem indBotEquivFinsupp_resIndBotIso_hom_hom_apply (X : Type u) [AddCommGroup X] [Module k X]
    (v : indBot k G X) (s : S) (y : G ⧸ S) :
    indBotEquivFinsupp k S (G ⧸ S →₀ X) ((resIndBotIso S X).hom.hom v) s y =
      indBotEquivFinsupp k G X v (y.out * s) := by
  rw [resIndBotIso, Rep.mkIso_hom_hom_apply, Representation.Equiv.coe_toLinearMap,
    Representation.Equiv.mk_apply]
  simp only [LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply, Finsupp.domLCongr_apply,
    Finsupp.domCongr_apply, Finsupp.curryLinearEquiv_apply, Finsupp.curry_apply,
    Finsupp.equivMapDomain_apply, Equiv.symm_trans_apply, Equiv.prodComm_symm,
    Equiv.prodComm_apply, Prod.swap_prod_mk, Subgroup.groupEquivQuotientProdSubgroup_symm_apply]

/-- The inverse of the restriction of an induced representation to `S`: the finitely supported
function on `G` attached to `W` evaluates `W` at the decomposition `g = ⟦g⟧.out * (⟦g⟧.out⁻¹ * g)`
of `g` into a coset and an element of `S`. -/
@[simp]
theorem indBotEquivFinsupp_resIndBotIso_inv_hom_apply (X : Type u) [AddCommGroup X] [Module k X]
    (W : indBot k S (G ⧸ S →₀ X)) (g : G) :
    indBotEquivFinsupp k G X ((resIndBotIso S X).inv.hom W) g =
      indBotEquivFinsupp k S (G ⧸ S →₀ X) W (Subgroup.groupEquivQuotientProdSubgroup g).2
        (Subgroup.groupEquivQuotientProdSubgroup g).1 := by
  rw [resIndBotIso, Rep.mkIso_inv_hom_apply, Representation.Equiv.mk_symm,
    Representation.Equiv.mk_apply]
  simp only [LinearEquiv.symm_trans_apply, LinearEquiv.apply_symm_apply, Finsupp.domLCongr_symm,
    Finsupp.domLCongr_apply, Finsupp.domCongr_apply, Finsupp.curryLinearEquiv_symm_apply,
    Finsupp.equivMapDomain_apply, Equiv.symm_symm, Equiv.trans_apply, Equiv.prodComm_apply,
    LinearEquiv.symm_symm, Finsupp.uncurry_apply, Prod.fst_swap, Prod.snd_swap]

end Restriction

end Rep
