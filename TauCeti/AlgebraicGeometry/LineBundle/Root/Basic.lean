/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.LineBundle.Power
public import TauCeti.CategoryTheory.Monoidal.TensorPow.Functor
public import TauCeti.CategoryTheory.Comma.StructuredArrow.Automorphisms
public import Mathlib.CategoryTheory.Limits.Shapes.IsTerminal
public import Mathlib.CategoryTheory.Core

/-!
# Roots of a line bundle

An `n`-th root of a line bundle `L` is a line bundle `M` together with an isomorphism
`M^{⊗n} ≅ L`. Its arrows are isomorphisms of `M` carrying one specified power isomorphism to
the other. Keeping these arrows, rather than just isomorphism classes, retains the inertia
needed for the gerbe of roots.

The construction is the category of costructured arrows for the tensor-power functor on the
core of invertible sheaves. The power functor uses `Functor.tensorPow` on constant tuples.
For a root `R`, `CostructuredArrow.autMulEquivKer R` identifies `Aut R` with the kernel of
the homomorphism on automorphism groups induced by `powerFunctor X n`.

## References

* E. Andreini, Y. Jiang and H.-H. Tseng, *Gromov–Witten theory of root gerbes I:
  structure of genus 0 moduli spaces*, §2.2, Definition 2.2.
-/

public section

open CategoryTheory MonoidalCategory
open _root_.AlgebraicGeometry

namespace TauCeti.AlgebraicGeometry.LineBundle

universe u

noncomputable section

variable {X : Scheme.{u}}

/-- The tensor-power functor on the core of invertible sheaves. Its objects use the
right-associated tensor-power convention `TauCeti.tensorPow`. -/
abbrev powerFunctor (X : Scheme.{u}) (n : ℕ) :
    Core (InvertibleSheaf X) ⥤ Core (InvertibleSheaf X) :=
  ((Functor.pi' (fun _ : Fin n ↦ 𝟭 (InvertibleSheaf X)) ⋙
    (𝟭 (InvertibleSheaf X)).tensorPow n).copyObj
      (fun M ↦ TauCeti.tensorPow M n)
      (fun M ↦ eqToIso ((𝟭 (InvertibleSheaf X)).tensorPow_obj_const M n))).core

@[simp]
lemma powerFunctor_obj (n : ℕ) (M : Core (InvertibleSheaf X)) :
    (powerFunctor X n).obj M = ⟨TauCeti.tensorPow M.of n⟩ := (rfl)

/-- The power functor acts on arrows by the specified tensor power of an isomorphism. -/
@[simp]
lemma powerFunctor_map_iso (n : ℕ) {M N : Core (InvertibleSheaf X)} (e : M ⟶ N) :
    ((powerFunctor X n).map e).iso = TauCeti.tensorPowMapIso e.iso n := by
  apply Iso.ext
  dsimp [powerFunctor, Functor.core, Core.functorToCore, Functor.copyObj]
  symm
  apply (conj_eqToHom_iff_heq' ..).mpr
  · simpa only [TauCeti.tensorPowMapIso_hom, Functor.pi', Functor.id_map, Functor.id_obj] using
      ((𝟭 (InvertibleSheaf X)).tensorPow_map_const e.iso.hom n).symm
  · simp [Functor.pi', Functor.tensorPow_obj_const]
  · simp [Functor.pi', Functor.tensorPow_obj_const]

/-- The groupoid of `n`-th roots of `L`: objects retain a line bundle and its power
isomorphism, and arrows commute with the power isomorphisms. -/
abbrev Root (L : InvertibleSheaf X) (n : ℕ) :=
  CostructuredArrow (powerFunctor X n) (Core.mk L)

namespace Root

variable {L K : InvertibleSheaf X} {n : ℕ}

/-- The category of roots is a groupoid, since its projection reflects isomorphisms. -/
instance : IsGroupoid (Root L n) :=
  isGroupoid_of_reflects_iso (CostructuredArrow.proj _ _)

/-- Forget the power isomorphism of a root. -/
abbrev projection (L : InvertibleSheaf X) (n : ℕ) :
    Root L n ⥤ Core (InvertibleSheaf X) := CostructuredArrow.proj _ _

/-- The invertible sheaf underlying a root. -/
abbrev lineBundle (R : Root L n) : InvertibleSheaf X := R.left.of

/-- The specified isomorphism from the tensor power of a root to `L`. -/
abbrev powerIso (R : Root L n) : TauCeti.tensorPow R.lineBundle n ≅ L := R.hom.iso

/-- Form a root from a line bundle and an isomorphism of its tensor power with `L`. -/
abbrev mk (M : InvertibleSheaf X) (φ : TauCeti.tensorPow M n ≅ L) : Root L n :=
  CostructuredArrow.mk (Y := Core.mk M) ⟨φ⟩

@[simp]
lemma lineBundle_mk (M : InvertibleSheaf X) (φ : TauCeti.tensorPow M n ≅ L) :
    (mk M φ).lineBundle = M := (rfl)

@[simp]
lemma powerIso_mk (M : InvertibleSheaf X) (φ : TauCeti.tensorPow M n ≅ L) :
    (mk M φ).powerIso = φ := (rfl)

/-- The defining triangle for an arrow of roots, in terms of tensor powers of
isomorphisms of invertible sheaves. -/
lemma arrow_w {R S : Root L n} (f : R ⟶ S) :
    TauCeti.tensorPowMapIso f.left.iso n ≪≫ S.powerIso = R.powerIso := by
  rw [← powerFunctor_map_iso]
  exact congrArg CoreHom.iso (CostructuredArrow.w f)

/-- Construct an arrow of roots from an isomorphism satisfying the defining triangle. -/
def homMk {R S : Root L n} (e : R.lineBundle ≅ S.lineBundle)
    (h : TauCeti.tensorPowMapIso e n ≪≫ S.powerIso = R.powerIso) : R ⟶ S :=
  CostructuredArrow.homMk ⟨e⟩ (by
    apply CoreHom.ext
    rw [coreCategory_comp_iso, powerFunctor_map_iso]
    exact h)

@[simp]
lemma homMk_left_iso {R S : Root L n} (e : R.lineBundle ≅ S.lineBundle)
    (h : TauCeti.tensorPowMapIso e n ≪≫ S.powerIso = R.powerIso) :
    (homMk e h).left.iso = e := (rfl)

/-- Arrows of roots are precisely the isomorphisms of their line bundles whose tensor
powers commute with the specified power isomorphisms. -/
def homEquiv (R S : Root L n) :
    (R ⟶ S) ≃ {e : R.lineBundle ≅ S.lineBundle //
      TauCeti.tensorPowMapIso e n ≪≫ S.powerIso = R.powerIso} where
  toFun f := ⟨f.left.iso, arrow_w f⟩
  invFun e := homMk e.val e.property
  left_inv f := by
    apply CostructuredArrow.hom_ext
    rfl
  right_inv e := by cases e; rfl

@[simp]
lemma homEquiv_apply_coe (R S : Root L n) (f : R ⟶ S) :
    (homEquiv R S f).val = f.left.iso := (rfl)

@[simp]
lemma homEquiv_symm_apply (R S : Root L n)
    (e : {e : R.lineBundle ≅ S.lineBundle //
      TauCeti.tensorPowMapIso e n ≪≫ S.powerIso = R.powerIso}) :
    (homEquiv R S).symm e = homMk e.val e.property := (rfl)

/-- An isomorphism of target line bundles transports their root groupoids. -/
abbrev mapIso (e : L ≅ K) (n : ℕ) : Root L n ≌ Root K n :=
  CostructuredArrow.mapIso (Core.isoMk e)

@[simp]
lemma mapIso_lineBundle (e : L ≅ K) (n : ℕ) (R : Root L n) :
    ((mapIso e n).functor.obj R).lineBundle = R.lineBundle := (rfl)

@[simp]
lemma mapIso_powerIso (e : L ≅ K) (n : ℕ) (R : Root L n) :
    ((mapIso e n).functor.obj R).powerIso = R.powerIso ≪≫ e := (rfl)

/-- The structure sheaf has its canonical trivial root for every exponent. -/
abbrev trivial (X : Scheme.{u}) (n : ℕ) : Root (InvertibleSheaf.trivial X) n :=
  mk (InvertibleSheaf.trivial X) (InvertibleSheaf.tensorPowTrivialIso X n)

/-- A line bundle has a root precisely when its Picard class is a power. -/
theorem nonempty_iff (L : InvertibleSheaf X) (n : ℕ) :
    Nonempty (Root L n) ↔ ∃ a : LineBundleClass X, a ^ n = LineBundleClass.mk L := by
  constructor
  · rintro ⟨R⟩
    refine ⟨LineBundleClass.mk R.lineBundle, ?_⟩
    rw [← LineBundleClass.mk_tensorPow, LineBundleClass.mk_eq_mk_iff]
    exact ⟨(SheafOfModules.isInvertible X).ι.mapIso R.powerIso⟩
  · rintro ⟨a, ha⟩
    obtain ⟨M, rfl⟩ := LineBundleClass.mk_surjective a
    rw [← LineBundleClass.mk_tensorPow, LineBundleClass.mk_eq_mk_iff] at ha
    obtain ⟨φ⟩ := ha
    exact ⟨mk M (ObjectProperty.isoMk _ φ)⟩

/-- The canonical first root of `L`, with the right unitor as its power isomorphism. -/
abbrev one (L : InvertibleSheaf X) : Root L 1 := mk L (ρ_ L)

/-- The canonical first root is terminal: every first root maps to it uniquely. -/
def isTerminalOne (L : InvertibleSheaf X) : Limits.IsTerminal (one L) := by
  refine Limits.IsTerminal.ofUniqueHom
    (fun R : Root L 1 ↦ homMk ((ρ_ R.lineBundle).symm ≪≫ R.powerIso) ?_) ?_
  · apply Iso.ext
    simp only [Iso.trans_hom, Iso.symm_hom, powerIso_mk, TauCeti.tensorPowMapIso_hom,
      TauCeti.tensorPowMap_succ, TauCeti.tensorPowMap_zero, tensorHom_id,
      rightUnitor_naturality]
    apply ObjectProperty.hom_ext
    simp
  · intro R f
    apply CostructuredArrow.hom_ext
    apply Core.hom_ext
    have h := congrArg Iso.hom (arrow_w f)
    simp only [Iso.trans_hom, TauCeti.tensorPowMapIso_hom, TauCeti.tensorPowMap_succ,
      TauCeti.tensorPowMap_zero, tensorHom_id] at h
    apply (cancel_epi (ρ_ R.lineBundle).hom).mp
    simpa only [homMk_left_iso, Iso.trans_hom, Iso.symm_hom, powerIso_mk,
      lineBundle_mk, rightUnitor_naturality,
      Iso.inv_hom_id_assoc, Iso.hom_inv_id_assoc] using h

/-- An arrow between zeroth roots preserves their trivializations of the tensor unit. -/
lemma zero_powerIso_eq {R S : Root L 0} (f : R ⟶ S) : R.powerIso = S.powerIso := by
  apply Iso.ext
  have h := congrArg Iso.hom (arrow_w f)
  simpa only [Iso.trans_hom, TauCeti.tensorPowMapIso_hom, TauCeti.tensorPowMap_zero,
    Category.id_comp] using h.symm

/-- Zeroth roots remember an arbitrary line bundle and a trivialization `𝟙 ≅ L`.
There are arrows only between roots with the same trivialization. -/
private def zeroFunctor (L : InvertibleSheaf X) :
    Root L 0 ⥤ Core (InvertibleSheaf X) × Discrete (𝟙_ (InvertibleSheaf X) ≅ L) where
  obj R := (R.left, Discrete.mk R.powerIso)
  map f := (f.left, eqToHom (congrArg Discrete.mk (zero_powerIso_eq f)))

/-- A line bundle and a trivialization of `L` give a zeroth root of `L`. -/
private def zeroInverse (L : InvertibleSheaf X) :
    Core (InvertibleSheaf X) × Discrete (𝟙_ (InvertibleSheaf X) ≅ L) ⥤ Root L 0 where
  obj p := mk p.1.of p.2.as
  map {p q} f := homMk f.1.iso (by
    have h : p.2.as = q.2.as := f.2.eq
    apply Iso.ext
    simpa only [Iso.trans_hom, TauCeti.tensorPowMapIso_hom,
      TauCeti.tensorPowMap_zero, Category.id_comp, powerIso_mk,
      TauCeti.tensorPow_zero] using congrArg Iso.hom h.symm)

/-- The zeroth-root groupoid is the product of the core of invertible sheaves and the
discrete category of trivializations of `L`. -/
def zeroEquivalence (L : InvertibleSheaf X) :
    Root L 0 ≌ Core (InvertibleSheaf X) × Discrete (𝟙_ (InvertibleSheaf X) ≅ L) where
  functor := zeroFunctor L
  inverse := zeroInverse L
  unitIso := NatIso.ofComponents
    (fun R ↦ CostructuredArrow.isoMk (Iso.refl _) (by
      simp [zeroFunctor, zeroInverse, mk, powerIso]
      rfl))
    (by
      intros
      apply CostructuredArrow.hom_ext
      simp [zeroFunctor, zeroInverse, homMk]
      rfl)
  counitIso := NatIso.ofComponents (fun _ ↦ Iso.refl _) (by
      intro p q f
      apply Prod.ext
      · simp [zeroFunctor, zeroInverse, homMk]
        rfl
      · apply Subsingleton.elim)

@[simp]
lemma zeroEquivalence_functor_obj (L : InvertibleSheaf X) (R : Root L 0) :
    (zeroEquivalence L).functor.obj R = (R.left, Discrete.mk R.powerIso) := (rfl)

@[simp]
lemma zeroEquivalence_inverse_obj (L : InvertibleSheaf X)
    (M : Core (InvertibleSheaf X)) (φ : 𝟙_ (InvertibleSheaf X) ≅ L) :
    (zeroEquivalence L).inverse.obj (M, Discrete.mk φ) = mk (n := 0) M.of φ := (rfl)

@[simp]
lemma zeroEquivalence_functor_map_fst_heq {R S : Root L 0} (f : R ⟶ S) :
    ((zeroEquivalence L).functor.map f).1 ≍ f.left := (HEq.rfl)

@[simp]
lemma zeroEquivalence_inverse_map_left_heq
    {p q : Core (InvertibleSheaf X) × Discrete (𝟙_ (InvertibleSheaf X) ≅ L)} (f : p ⟶ q) :
    ((zeroEquivalence L).inverse.map f).left ≍ f.1 := (HEq.rfl)

end Root

end

end TauCeti.AlgebraicGeometry.LineBundle
