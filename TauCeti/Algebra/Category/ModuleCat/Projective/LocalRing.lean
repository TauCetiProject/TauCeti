/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Projective
public import Mathlib.CategoryTheory.Retract
public import TauCeti.RingTheory.LocalRing.Module
import Mathlib.RingTheory.Nakayama

/-!
# Projective retracts over a local ring

A finite module over a local ring that admits a nonzero projective retract also admits `R` itself
as a retract (`CategoryTheory.Retract.nonempty_retract_ring_of_projective`), since a finitely
generated projective module over a local ring is free.

Over any commutative ring, if a retract `ret : Retract P K` of a finitely generated module `P` has
its retraction extending across a map `i : K ⟶ F` whose range lies in `Ring.jacobson R • ⊤`, then
`P` is zero by Nakayama's lemma
(`CategoryTheory.Retract.isZero_of_range_le_jacobson_smul_of_comp_eq`).

## Main results

* `CategoryTheory.Retract.nonempty_retract_ring_of_projective`: a nonzero projective retract of a
  finite module over a local ring produces a retract from `R`.
* `CategoryTheory.Retract.isZero_of_range_le_jacobson_smul_of_comp_eq`: a retract of a module
  whose retraction extends across a map into `Ring.jacobson R • ⊤` has zero finite domain.
-/

public section

universe u v

open CategoryTheory

namespace CategoryTheory.Retract

/-- A nonzero projective retract of a finite module over a local ring `R` yields a retract of `R`
itself into the module. -/
theorem nonempty_retract_ring_of_projective {R : Type u} [CommRing R] [_root_.IsLocalRing R]
    {M P : ModuleCat.{u} R} [Module.Finite R M] [Projective P] [Nontrivial P]
    (ret : Retract P M) :
    Nonempty (Retract (ModuleCat.of R R) M) := by
  have : Module.Finite R P := .of_surjective ret.r.hom
    (Function.LeftInverse.surjective fun p ↦ ConcreteCategory.congr_hom ret.retract p)
  have : Module.Projective R P := (IsProjective.iff_projective P).2 inferInstance
  have : Module.Free R P := Module.free_of_projective_of_isLocalRing
  let b := Module.Free.chooseBasis R P
  obtain ⟨i₀⟩ : Nonempty (Module.Free.ChooseBasisIndex R P) := by
    by_contra! hemp
    exact not_subsingleton P b.repr.subsingleton
  let _ := Classical.decEq (Module.Free.ChooseBasisIndex R P)
  refine ⟨Retract.trans
    { i := ModuleCat.ofHom (LinearMap.toSpanSingleton R P (b i₀))
      r := ModuleCat.ofHom (b.coord i₀)
      retract := ModuleCat.hom_ext <| LinearMap.ext fun r ↦ by
        simp [b.coord_apply] }
    ret⟩

/-- **Nakayama criterion for retracts.** If `ret : Retract P K` has retraction extending across a
map `i : K ⟶ F` whose range lies in `Ring.jacobson R • ⊤`, and `P` is finitely generated, then
`P` is zero. -/
theorem isZero_of_range_le_jacobson_smul_of_comp_eq
    {R : Type u} [CommRing R] {K F P : ModuleCat.{v} R} [Module.Finite R P]
    {i : K ⟶ F} (hi_min : LinearMap.range i.hom ≤ Ring.jacobson R • ⊤)
    (ret : Retract P K) (g : F ⟶ P) (hg : i ≫ g = ret.r) : Limits.IsZero P := by
  have htop : (⊤ : Submodule R P) ≤ Ring.jacobson R • ⊤ := fun x _ ↦ by
    have hx : g.hom (i.hom (ret.i.hom x)) = x := by
      have hcomp : ret.i ≫ i ≫ g = 𝟙 P := by rw [hg, ret.retract]
      simpa only [ModuleCat.hom_comp, LinearMap.comp_apply, ModuleCat.hom_id,
        LinearMap.id_apply] using congrArg (fun f : P ⟶ P ↦ f.hom x) hcomp
    exact hx ▸ Submodule.smul_top_le_comap_smul_top (Ring.jacobson R) g.hom
      (hi_min ⟨ret.i.hom x, rfl⟩)
  have hbot := Submodule.eq_bot_of_le_smul_of_le_jacobson _ _ Module.Finite.fg_top htop le_rfl
  have : Subsingleton P :=
    subsingleton_of_forall_eq 0 fun x ↦ (Submodule.mem_bot R).1 (hbot ▸ Submodule.mem_top)
  exact ModuleCat.isZero_of_subsingleton P

end CategoryTheory.Retract
