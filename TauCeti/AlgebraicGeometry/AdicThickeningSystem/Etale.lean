/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.UniversalHomeomorphism
import Mathlib.AlgebraicGeometry.Morphisms.FormallyUnramified

/-!
# Étale morphisms over adic thickening systems

A morphism between étale schemes on the initial level of an adic thickening system extends
uniquely to a compatible family of morphisms on all infinitesimal levels. More generally, only
the target needs to be étale over the base system. Isomorphisms on the initial level extend to
isomorphisms when both systems are étale over the base.

These results construct the compatible infinitesimal morphisms used in formal comparison for
finite étale covers. They do not assert algebraization: recovering a morphism of schemes from
its infinitesimal restrictions requires a separate full-faithfulness theorem for completion.
Neither finiteness nor Noetherian hypotheses are needed for the infinitesimal construction.

## References

* Stacks Project, proof of Lemma 58.17.1 (0EL8), lifting a morphism of finite étale covers to
  all infinitesimal neighbourhoods before applying coherent full faithfulness.
* Stacks Project, Theorem 59.45.2 (04DZ), topological invariance of the small étale site.
-/

public section

open CategoryTheory AlgebraicGeometry

universe u

namespace TauCeti.AlgebraicGeometry.AdicThickeningSystem

variable {𝔛 𝔜 Z : AdicThickeningSystem.{u}}

/-- Morphisms over an adic thickening system into a levelwise formally unramified target are
determined by their initial component. The source need not be étale or adic over the base. -/
theorem hom_ext_of_formallyUnramified (q : Z ⟶ 𝔛)
    [∀ n, FormallyUnramified (q.app n)] {a b : 𝔜 ⟶ Z}
    (h : a ≫ q = b ≫ q) (h₀ : a.app 0 = b.app 0) : a = b := by
  ext n
  apply FormallyUnramified.hom_ext (𝔜.levelMap n)
    ⟨n + 1, 𝔜.ker_levelMap_pow_succ_eq_bot n⟩ (q.app n)
  · simp only [Hom.levelMap_app, h₀]
  · simpa using congrArg (fun f : 𝔜 ⟶ 𝔛 ↦ f.app n) h

/-- A morphism on the initial level into a levelwise étale target extends uniquely over an
adic thickening system. The resulting morphism commutes with the structure maps to the base
and restricts to the prescribed morphism on level zero. -/
theorem existsUnique_hom_of_etale (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (q.app n)] (a₀ : 𝔜.X 0 ⟶ Z.X 0)
    (ha₀ : a₀ ≫ q.app 0 = p.app 0) :
    ∃! a : 𝔜 ⟶ Z, a ≫ q = p ∧ a.app 0 = a₀ := by
  have lifts (n : ℕ) : ∃ a : 𝔜.X n ⟶ Z.X n,
      𝔜.levelMap n ≫ a = a₀ ≫ Z.levelMap n ∧ a ≫ q.app n = p.app n := by
    have sq : CommSq (a₀ ≫ Z.levelMap n) (𝔜.levelMap n) (q.app n) (p.app n) :=
      ⟨by simp only [Category.assoc, Hom.levelMap_app]; rw [← Category.assoc, ha₀]⟩
    exact ⟨sq.lift, sq.fac_left, sq.fac_right⟩
  choose a hleft hright using lifts
  have hzero : a 0 = a₀ := by simpa using hleft 0
  have hnat (n : ℕ) : 𝔜.ι n ≫ a (n + 1) = a n ≫ Z.ι n := by
    apply FormallyUnramified.hom_ext (𝔜.levelMap n)
      ⟨n + 1, 𝔜.ker_levelMap_pow_succ_eq_bot n⟩ (q.app (n + 1))
    · simpa only [levelMap_succ, Category.assoc, reassoc_of% hleft n] using hleft (n + 1)
    · simp only [Category.assoc, hright, Hom.naturality]
      rw [← Category.assoc, hright]
  let a' : 𝔜 ⟶ Z := { app := a, naturality := hnat }
  have ha' : a' ≫ q = p := hom_ext hright
  refine ⟨a', ⟨ha', hzero⟩, fun b hb ↦ ?_⟩
  exact hom_ext_of_formallyUnramified q (hb.1.trans ha'.symm) (hb.2.trans hzero.symm)

/-- The unique lift of an initial morphism into a levelwise étale target over the base. -/
noncomputable def liftOfEtale (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (q.app n)] (a₀ : 𝔜.X 0 ⟶ Z.X 0)
    (ha₀ : a₀ ≫ q.app 0 = p.app 0) : 𝔜 ⟶ Z :=
  (existsUnique_hom_of_etale p q a₀ ha₀).exists.choose

@[reassoc (attr := simp)]
theorem liftOfEtale_comp (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (q.app n)] (a₀ : 𝔜.X 0 ⟶ Z.X 0)
    (ha₀ : a₀ ≫ q.app 0 = p.app 0) : liftOfEtale p q a₀ ha₀ ≫ q = p :=
  (existsUnique_hom_of_etale p q a₀ ha₀).exists.choose_spec.1

@[simp]
theorem liftOfEtale_app_zero (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (q.app n)] (a₀ : 𝔜.X 0 ⟶ Z.X 0)
    (ha₀ : a₀ ≫ q.app 0 = p.app 0) : (liftOfEtale p q a₀ ha₀).app 0 = a₀ :=
  (existsUnique_hom_of_etale p q a₀ ha₀).exists.choose_spec.2

/-- Any morphism over the base with the prescribed initial component is the étale lift. -/
theorem eq_liftOfEtale (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (q.app n)] (a₀ : 𝔜.X 0 ⟶ Z.X 0)
    (ha₀ : a₀ ≫ q.app 0 = p.app 0) {a : 𝔜 ⟶ Z}
    (ha : a ≫ q = p) (h₀ : a.app 0 = a₀) : a = liftOfEtale p q a₀ ha₀ :=
  hom_ext_of_formallyUnramified q (ha.trans (liftOfEtale_comp p q a₀ ha₀).symm)
    (h₀.trans (liftOfEtale_app_zero p q a₀ ha₀).symm)

@[reassoc (attr := simp)]
theorem liftOfEtale_app_comp (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (q.app n)] (a₀ : 𝔜.X 0 ⟶ Z.X 0)
    (ha₀ : a₀ ≫ q.app 0 = p.app 0) (n : ℕ) :
    (liftOfEtale p q a₀ ha₀).app n ≫ q.app n = p.app n := by
  simpa only [comp_app] using
    congrArg (fun f : 𝔜 ⟶ 𝔛 ↦ f.app n) (liftOfEtale_comp p q a₀ ha₀)

@[simp]
theorem liftOfEtale_id (p : 𝔜 ⟶ 𝔛) [∀ n, Etale (p.app n)] :
    liftOfEtale p p (𝟙 _) (by simp) = 𝟙 𝔜 := by
  exact (eq_liftOfEtale p p (𝟙 _) (by simp) (by simp) (by simp)).symm

@[reassoc (attr := simp)]
theorem liftOfEtale_comp_liftOfEtale {W : AdicThickeningSystem.{u}}
    (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛) (r : W ⟶ 𝔛)
    [∀ n, Etale (q.app n)] [∀ n, Etale (r.app n)]
    (a₀ : 𝔜.X 0 ⟶ Z.X 0) (ha₀ : a₀ ≫ q.app 0 = p.app 0)
    (b₀ : Z.X 0 ⟶ W.X 0) (hb₀ : b₀ ≫ r.app 0 = q.app 0) :
    liftOfEtale p q a₀ ha₀ ≫ liftOfEtale q r b₀ hb₀ =
      liftOfEtale p r (a₀ ≫ b₀) (by rw [Category.assoc, hb₀, ha₀]) := by
  apply eq_liftOfEtale <;> simp

/-- The unique lift of an initial isomorphism between levelwise étale systems over the base. -/
noncomputable def isoOfEtale (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) : 𝔜 ≅ Z :=
  { hom := liftOfEtale p q e₀.hom he₀
    inv := liftOfEtale q p e₀.inv (by rw [← he₀, Iso.inv_hom_id_assoc])
    hom_inv_id := by
      apply hom_ext_of_formallyUnramified p (by simp)
      simp
    inv_hom_id := by
      apply hom_ext_of_formallyUnramified q (by simp)
      simp }

/-- The forward map of the lifted isomorphism is the lift of its initial forward map. -/
theorem isoOfEtale_hom (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    (isoOfEtale p q e₀ he₀).hom = liftOfEtale p q e₀.hom he₀ :=
  (rfl)

/-- The inverse of the lifted isomorphism is the lift of its initial inverse. -/
theorem isoOfEtale_inv (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    (isoOfEtale p q e₀ he₀).inv =
      liftOfEtale q p e₀.inv (by rw [← he₀, Iso.inv_hom_id_assoc]) :=
  (rfl)

@[simp]
theorem isoOfEtale_hom_app_zero (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    (isoOfEtale p q e₀ he₀).hom.app 0 = e₀.hom := by
  rw [isoOfEtale_hom, liftOfEtale_app_zero]

@[reassoc (attr := simp)]
theorem isoOfEtale_hom_comp (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    (isoOfEtale p q e₀ he₀).hom ≫ q = p := by
  rw [isoOfEtale_hom, liftOfEtale_comp]

@[simp]
theorem isoOfEtale_inv_app_zero (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    (isoOfEtale p q e₀ he₀).inv.app 0 = e₀.inv := by
  rw [isoOfEtale_inv, liftOfEtale_app_zero]

@[reassoc (attr := simp)]
theorem isoOfEtale_inv_comp (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    (isoOfEtale p q e₀ he₀).inv ≫ p = q := by
  rw [isoOfEtale_inv, liftOfEtale_comp]

@[reassoc (attr := simp)]
theorem isoOfEtale_hom_app_comp (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) (n : ℕ) :
    (isoOfEtale p q e₀ he₀).hom.app n ≫ q.app n = p.app n := by
  rw [isoOfEtale_hom, liftOfEtale_app_comp]

@[reassoc (attr := simp)]
theorem isoOfEtale_inv_app_comp (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) (n : ℕ) :
    (isoOfEtale p q e₀ he₀).inv.app n ≫ p.app n = q.app n := by
  rw [isoOfEtale_inv, liftOfEtale_app_comp]

/-- Any isomorphism over the base with the prescribed initial component is the étale lift. -/
theorem eq_isoOfEtale (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) {e : 𝔜 ≅ Z}
    (he : e.hom ≫ q = p) (h₀ : e.hom.app 0 = e₀.hom) : e = isoOfEtale p q e₀ he₀ := by
  apply Iso.ext
  rw [isoOfEtale_hom]
  exact eq_liftOfEtale p q e₀.hom he₀ he h₀

/-- An isomorphism on the initial level between two levelwise étale systems over the same base
extends uniquely to an isomorphism of systems over that base. -/
theorem existsUnique_iso_of_etale (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    ∃! e : 𝔜 ≅ Z, e.hom ≫ q = p ∧ e.hom.app 0 = e₀.hom := by
  exact ⟨isoOfEtale p q e₀ he₀, ⟨by simp, by simp⟩,
    fun e he ↦ eq_isoOfEtale p q e₀ he₀ he.1 he.2⟩

/-- Lifting an initial isomorphism between levelwise étale systems gives an isomorphism. -/
instance (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (a₀ : 𝔜.X 0 ⟶ Z.X 0) [IsIso a₀] (ha₀ : a₀ ≫ q.app 0 = p.app 0) :
    IsIso (liftOfEtale p q a₀ ha₀) := by
  have h := isoOfEtale_hom p q (asIso a₀) (by simpa using ha₀)
  simp only [asIso_hom] at h
  rw [← h]
  infer_instance

@[simp]
theorem isoOfEtale_refl (p : 𝔜 ⟶ 𝔛) [∀ n, Etale (p.app n)] :
    isoOfEtale p p (Iso.refl _) (by simp) = Iso.refl 𝔜 := by
  exact (eq_isoOfEtale p p (Iso.refl _) (by simp) (by simp) (by simp)).symm

/-- Lifting the inverse initial isomorphism gives the inverse of the lifted isomorphism. -/
theorem isoOfEtale_symm (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    (isoOfEtale p q e₀ he₀).symm =
      isoOfEtale q p e₀.symm (by rw [Iso.symm_hom, ← he₀, Iso.inv_hom_id_assoc]) := by
  apply eq_isoOfEtale <;> simp

@[simp]
theorem isoOfEtale_trans {W : AdicThickeningSystem.{u}}
    (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛) (r : W ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)] [∀ n, Etale (r.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0)
    (f₀ : Z.X 0 ≅ W.X 0) (hf₀ : f₀.hom ≫ r.app 0 = q.app 0) :
    isoOfEtale p q e₀ he₀ ≪≫ isoOfEtale q r f₀ hf₀ =
      isoOfEtale p r (e₀ ≪≫ f₀) (by simp [hf₀, he₀]) := by
  apply eq_isoOfEtale <;> simp

end TauCeti.AlgebraicGeometry.AdicThickeningSystem
