/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.AdicThickeningSystem.Basic
public import TauCeti.AlgebraicGeometry.Morphisms.Etale.UniversalHomeomorphism
import TauCeti.AlgebraicGeometry.Morphisms.FormallyUnramified

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

/-- Morphisms over an adic thickening system into a levelwise unramified target are determined
by their initial component. The source need not be étale or adic over the base. -/
theorem hom_ext_of_formallyUnramified (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, FormallyUnramified (q.app n)] [∀ n, LocallyOfFiniteType (q.app n)]
    {a b : 𝔜 ⟶ Z}
    (ha : a ≫ q = p) (hb : b ≫ q = p) (h₀ : a.app 0 = b.app 0) : a = b := by
  ext n
  apply _root_.AlgebraicGeometry.ext_of_surjective_of_formallyUnramified (q.app n)
    (by simpa using congrArg (fun f : 𝔜 ⟶ 𝔛 ↦ f.app n) (ha.trans hb.symm))
    (𝔜.levelMap n)
  simp only [Hom.levelMap_app, h₀]

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
    apply _root_.AlgebraicGeometry.ext_of_surjective_of_formallyUnramified (q.app (n + 1))
      (by
        simp only [Category.assoc, hright, Hom.naturality]
        rw [← Category.assoc, hright]) (𝔜.levelMap n)
    simpa only [levelMap_succ, Category.assoc, reassoc_of% hleft n] using hleft (n + 1)
  let a' : 𝔜 ⟶ Z := { app := a, naturality := hnat }
  have ha' : a' ≫ q = p := hom_ext hright
  refine ⟨a', ⟨ha', hzero⟩, fun b hb ↦ ?_⟩
  exact hom_ext_of_formallyUnramified p q hb.1 ha' (hb.2.trans hzero.symm)

/-- An isomorphism on the initial level between two levelwise étale systems over the same base
extends uniquely to an isomorphism of systems over that base. -/
theorem existsUnique_iso_of_etale (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    ∃! e : 𝔜 ≅ Z, e.hom ≫ q = p ∧ e.hom.app 0 = e₀.hom := by
  obtain ⟨a, ha, -⟩ := existsUnique_hom_of_etale p q e₀.hom he₀
  obtain ⟨b, hb, -⟩ := existsUnique_hom_of_etale q p e₀.inv
    (by rw [← he₀, Iso.inv_hom_id_assoc])
  have hab : a ≫ b = 𝟙 𝔜 := by
    apply hom_ext_of_formallyUnramified p p (by simp [ha.1, hb.1]) (by simp)
    simp [ha.2, hb.2]
  have hba : b ≫ a = 𝟙 Z := by
    apply hom_ext_of_formallyUnramified q q (by simp [ha.1, hb.1]) (by simp)
    simp [ha.2, hb.2]
  refine ⟨⟨a, b, hab, hba⟩, ha, fun e he ↦ ?_⟩
  exact Iso.ext (hom_ext_of_formallyUnramified p q he.1 ha.1 (he.2.trans ha.2.symm))

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
  hom_ext_of_formallyUnramified p q ha (liftOfEtale_comp p q a₀ ha₀)
    (h₀.trans (liftOfEtale_app_zero p q a₀ ha₀).symm)

/-- The unique lift of an initial isomorphism between levelwise étale systems over the base. -/
noncomputable def isoOfEtale (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) : 𝔜 ≅ Z :=
  (existsUnique_iso_of_etale p q e₀ he₀).exists.choose

@[simp]
theorem isoOfEtale_hom_app_zero (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    (isoOfEtale p q e₀ he₀).hom.app 0 = e₀.hom :=
  (existsUnique_iso_of_etale p q e₀ he₀).exists.choose_spec.2

@[reassoc (attr := simp)]
theorem isoOfEtale_hom_comp (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    (isoOfEtale p q e₀ he₀).hom ≫ q = p :=
  (existsUnique_iso_of_etale p q e₀ he₀).exists.choose_spec.1

@[simp]
theorem isoOfEtale_inv_app_zero (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    (isoOfEtale p q e₀ he₀).inv.app 0 = e₀.inv := by
  apply (cancel_mono e₀.hom).mp
  calc
    _ = (isoOfEtale p q e₀ he₀).inv.app 0 ≫ (isoOfEtale p q e₀ he₀).hom.app 0 := by
      rw [isoOfEtale_hom_app_zero]
    _ = 𝟙 _ := by rw [← comp_app, Iso.inv_hom_id, id_app]
    _ = e₀.inv ≫ e₀.hom := e₀.inv_hom_id.symm

@[reassoc (attr := simp)]
theorem isoOfEtale_inv_comp (p : 𝔜 ⟶ 𝔛) (q : Z ⟶ 𝔛)
    [∀ n, Etale (p.app n)] [∀ n, Etale (q.app n)]
    (e₀ : 𝔜.X 0 ≅ Z.X 0) (he₀ : e₀.hom ≫ q.app 0 = p.app 0) :
    (isoOfEtale p q e₀ he₀).inv ≫ p = q := by
  calc
    _ = (isoOfEtale p q e₀ he₀).inv ≫ ((isoOfEtale p q e₀ he₀).hom ≫ q) := by
      rw [isoOfEtale_hom_comp]
    _ = q := Iso.inv_hom_id_assoc _ _

end TauCeti.AlgebraicGeometry.AdicThickeningSystem
