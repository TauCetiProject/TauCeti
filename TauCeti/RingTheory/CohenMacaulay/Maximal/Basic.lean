/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.CategoryTheory.Exact.ExtensionClosed
public import TauCeti.RingTheory.CohenMacaulay.Basic
import Mathlib.Algebra.Category.ModuleCat.Biproducts
import TauCeti.RingTheory.LocalRing.Module

/-!
# Maximal Cohen–Macaulay modules and their exact category

A module `M` over a local ring `R` is *maximal Cohen–Macaulay* (`Module.IsMaximalCohenMacaulay R M`)
if `M = 0` or `depth M = ringKrullDim R`. For finite modules over a Noetherian local ring this is
equivalent to `ringKrullDim R ≤ depth M` (`isMaximalCohenMacaulay_iff_ringKrullDim_le_depth`).
Closure under extensions, binary products, retracts, and syzygies equips the full subcategory
`TauCeti.MaximalCohenMacaulayModuleCat R` with `MaximalCohenMacaulayModuleCat.exactStructure`.

## References

* W. Bruns and J. Herzog, *Cohen–Macaulay Rings*, Cambridge Univ. Press (1993), Section 2.1.
* R.-O. Buchweitz, *Maximal Cohen–Macaulay Modules and Tate Cohomology*, AMS (2021), Section 4.
* [The Stacks Project, Section 10.104](https://stacks.math.columbia.edu/tag/00NF).
-/

public section

universe v u w

open CategoryTheory CategoryTheory.Limits IsLocalRing

namespace Module

variable (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R]
  (M : Type v) [AddCommGroup M] [Module R M]

/-- An `R`-module `M` is *maximal Cohen–Macaulay* if `M = 0` or `depth M = ringKrullDim R`. -/
def IsMaximalCohenMacaulay : Prop :=
  Subsingleton M ∨ (depth (ModuleCat.of R M) : WithBot ℕ∞) = ringKrullDim R

/-- Unfolds `Module.IsMaximalCohenMacaulay`. -/
theorem isMaximalCohenMacaulay_iff : IsMaximalCohenMacaulay R M ↔
    Subsingleton M ∨ (depth (ModuleCat.of R M) : WithBot ℕ∞) = ringKrullDim R := Iff.rfl

variable {R M}

/-- The zero module is maximal Cohen–Macaulay. -/
theorem isMaximalCohenMacaulay_of_subsingleton [Subsingleton M] : IsMaximalCohenMacaulay R M :=
  Or.inl ‹_›

/-- A nonzero module is maximal Cohen–Macaulay if and only if its depth equals `ringKrullDim R`. -/
theorem isMaximalCohenMacaulay_iff_depth_eq [Nontrivial M] :
    IsMaximalCohenMacaulay R M ↔ (depth (ModuleCat.of R M) : WithBot ℕ∞) = ringKrullDim R := by
  rw [isMaximalCohenMacaulay_iff, or_iff_right (not_subsingleton M)]

/-- The depth of a nonzero maximal Cohen–Macaulay module equals `ringKrullDim R`. -/
theorem IsMaximalCohenMacaulay.depth_eq [Nontrivial M] (h : IsMaximalCohenMacaulay R M) :
    (depth (ModuleCat.of R M) : WithBot ℕ∞) = ringKrullDim R :=
  isMaximalCohenMacaulay_iff_depth_eq.1 h

/-- Every maximal Cohen–Macaulay module has depth at least `ringKrullDim R`. -/
theorem IsMaximalCohenMacaulay.ringKrullDim_le_depth (h : IsMaximalCohenMacaulay R M) :
    ringKrullDim R ≤ (depth (ModuleCat.of R M) : WithBot ℕ∞) := by
  rcases h with _ | heq
  · simp only [IsLocalRing.depth, Ideal.depth_eq_top_of_subsingleton, WithBot.coe_top, le_top]
  · exact heq.symm.le

/-- A Cohen–Macaulay module of support dimension `ringKrullDim R` is maximal Cohen–Macaulay. -/
theorem IsCohenMacaulay.isMaximalCohenMacaulay (hM : IsCohenMacaulay R M)
    (hdim : supportDim R M = ringKrullDim R) : IsMaximalCohenMacaulay R M := by
  cases subsingleton_or_nontrivial M
  · exact isMaximalCohenMacaulay_of_subsingleton
  · exact isMaximalCohenMacaulay_iff_depth_eq.2 (hM.depth_eq.trans hdim)

/-- A local ring is maximal Cohen–Macaulay over itself if and only if it is Cohen–Macaulay. -/
theorem isMaximalCohenMacaulay_self_iff {A : Type u} [CommRing A] [IsLocalRing A] :
    IsMaximalCohenMacaulay A A ↔ IsCohenMacaulay A A := by
  rw [isMaximalCohenMacaulay_iff_depth_eq, isCohenMacaulay_iff_depth_eq,
    supportDim_self_eq_ringKrullDim]

/-- Over a Cohen–Macaulay local ring, every finite free module is maximal Cohen–Macaulay. -/
theorem IsCohenMacaulay.isMaximalCohenMacaulay_of_free (hR : IsCohenMacaulay R R)
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Free R N] [Module.Finite R N] :
    IsMaximalCohenMacaulay R N := by
  cases subsingleton_or_nontrivial N
  · exact isMaximalCohenMacaulay_of_subsingleton
  · rw [isMaximalCohenMacaulay_iff_depth_eq, depth_eq_depth_self_of_free N]
    exact (isMaximalCohenMacaulay_self_iff.2 hR).depth_eq

/-- Over a Cohen–Macaulay local ring, every finite projective module is maximal Cohen–Macaulay. -/
theorem IsCohenMacaulay.isMaximalCohenMacaulay_of_projective (hR : IsCohenMacaulay R R)
    (N : Type v) [AddCommGroup N] [Module R N] [Module.Projective R N] [Module.Finite R N] :
    IsMaximalCohenMacaulay R N :=
  have := Module.free_of_projective_of_isLocalRing (R := R) (M := N)
  hR.isMaximalCohenMacaulay_of_free N

section Noetherian

variable [IsNoetherianRing R] [Module.Finite R M]

/-- For a finite module over a Noetherian local ring, maximal Cohen–Macaulayness is equivalent to
`ringKrullDim R ≤ depth M`. -/
theorem isMaximalCohenMacaulay_iff_ringKrullDim_le_depth :
    IsMaximalCohenMacaulay R M ↔ ringKrullDim R ≤ (depth (ModuleCat.of R M) : WithBot ℕ∞) := by
  refine ⟨IsMaximalCohenMacaulay.ringKrullDim_le_depth, fun h ↦ ?_⟩
  cases subsingleton_or_nontrivial M
  · exact isMaximalCohenMacaulay_of_subsingleton
  · exact isMaximalCohenMacaulay_iff_depth_eq.2 <|
      le_antisymm (depth_le_supportDim.trans (supportDim_le_ringKrullDim R M)) h

/-- Every finite maximal Cohen–Macaulay module over a Noetherian local ring is Cohen–Macaulay. -/
theorem IsMaximalCohenMacaulay.isCohenMacaulay (h : IsMaximalCohenMacaulay R M) :
    IsCohenMacaulay R M := by
  cases subsingleton_or_nontrivial M
  · exact isCohenMacaulay_of_subsingleton
  · exact isCohenMacaulay_iff_supportDim_le_depth.2 <|
      (supportDim_le_ringKrullDim R M).trans h.ringKrullDim_le_depth

/-- A nonzero finite maximal Cohen–Macaulay module over a Noetherian local ring has support of full
dimension `ringKrullDim R`. -/
theorem IsMaximalCohenMacaulay.supportDim_eq_ringKrullDim [Nontrivial M]
    (h : IsMaximalCohenMacaulay R M) : supportDim R M = ringKrullDim R :=
  le_antisymm (supportDim_le_ringKrullDim R M) (h.depth_eq ▸ depth_le_supportDim)

end Noetherian
end Module

namespace LinearEquiv

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R] [Small.{w} R]
  {M : Type v} [AddCommGroup M] [Module R M] {N : Type w} [AddCommGroup N] [Module R N]

/-- Being maximal Cohen–Macaulay is invariant under linear equivalence. -/
theorem isMaximalCohenMacaulay_iff (e : M ≃ₗ[R] N) :
    Module.IsMaximalCohenMacaulay R M ↔ Module.IsMaximalCohenMacaulay R N := by
  rw [Module.isMaximalCohenMacaulay_iff, Module.isMaximalCohenMacaulay_iff,
    e.toEquiv.subsingleton_congr, depth_eq_of_linearEquiv e]

end LinearEquiv

namespace RingEquiv

variable {R : Type u} {S : Type v} [CommRing R] [CommRing S] [IsLocalRing R] [IsLocalRing S]

/-- A local ring is maximal Cohen–Macaulay over itself if and only if an isomorphic ring is. -/
theorem isMaximalCohenMacaulay_self_iff (e : R ≃+* S) :
    Module.IsMaximalCohenMacaulay R R ↔ Module.IsMaximalCohenMacaulay S S := by
  rw [Module.isMaximalCohenMacaulay_self_iff, Module.isMaximalCohenMacaulay_self_iff,
    e.isCohenMacaulay_self_iff]

end RingEquiv

namespace Module.IsMaximalCohenMacaulay

variable {R : Type u} [CommRing R] [IsLocalRing R] [Small.{v} R]

/-- In a short exact sequence `0 → M → N → Q → 0` over a local ring, if `M` and `Q` are maximal
Cohen–Macaulay, then so is `N`. -/
theorem of_exact_middle {M N Q : Type v} [AddCommGroup M] [Module R M]
    [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hM : IsMaximalCohenMacaulay R M) (hQ : IsMaximalCohenMacaulay R Q) :
    IsMaximalCohenMacaulay R N := by
  cases subsingleton_or_nontrivial M
  · refine (LinearEquiv.ofBijective g ⟨?_, hg⟩).isMaximalCohenMacaulay_iff.2 hQ
    rw [← LinearMap.ker_eq_bot, hfg.linearMap_ker_eq,
      LinearMap.range_eq_bot.2 (Subsingleton.elim _ _)]
  · cases subsingleton_or_nontrivial Q
    · exact (LinearEquiv.ofBijective f ⟨hf, fun n ↦ (hfg n).1 (Subsingleton.elim _ 0)⟩)
        |>.isMaximalCohenMacaulay_iff.1 hM
    · have : Nontrivial N := hg.nontrivial
      have hge : ringKrullDim R ≤ (depth (ModuleCat.of R N) : WithBot ℕ∞) :=
        (le_inf hM.ringKrullDim_le_depth hQ.ringKrullDim_le_depth).trans <| by
          rw [← WithBot.coe_inf]
          exact WithBot.coe_le_coe.2 (depth_min_fst_trd_le_snd_of_exact f g hfg hf hg)
      have hmin := depth_min_snd_trd_add_one_le_fst_of_exact f g hfg hf hg
      rw [WithBot.coe_inj.1 (hQ.depth_eq.trans hM.depth_eq.symm)] at hmin
      refine isMaximalCohenMacaulay_iff_depth_eq.2 (le_antisymm (hM.depth_eq ▸ ?_) hge)
      rw [WithBot.coe_le_coe]
      induction hd : depth (ModuleCat.of R M) using ENat.recTopCoe with
      | top => exact le_top
      | coe k =>
        rw [hd] at hmin
        by_contra! hlt
        exact absurd (by exact_mod_cast (le_inf (Order.add_one_le_of_lt hlt) le_rfl).trans hmin :
          k + 1 ≤ k) (by omega)

/-- Binary products of maximal Cohen–Macaulay modules are maximal Cohen–Macaulay. -/
theorem prod {M N : Type v} [AddCommGroup M] [Module R M] [AddCommGroup N] [Module R N]
    (hM : IsMaximalCohenMacaulay R M) (hN : IsMaximalCohenMacaulay R N) :
    IsMaximalCohenMacaulay R (M × N) :=
  hM.of_exact_middle Function.Exact.inl_snd LinearMap.inl_injective LinearMap.snd_surjective hN

/-- In a short exact sequence `0 → M → N → Q → 0` with `M` finite over a Noetherian local ring, if
`N` is maximal Cohen–Macaulay and `ringKrullDim R ≤ depth Q + 1`, then `M` is maximal
Cohen–Macaulay. -/
theorem of_exact_left [IsNoetherianRing R] {M N Q : Type v} [AddCommGroup M] [Module R M]
    [Module.Finite R M] [AddCommGroup N] [Module R N] [AddCommGroup Q] [Module R Q]
    {f : M →ₗ[R] N} {g : N →ₗ[R] Q} (hfg : Function.Exact f g)
    (hf : Function.Injective f) (hg : Function.Surjective g)
    (hN : IsMaximalCohenMacaulay R N)
    (hQ : ringKrullDim R ≤ (depth (ModuleCat.of R Q) : WithBot ℕ∞) + 1) :
    IsMaximalCohenMacaulay R M := by
  rw [isMaximalCohenMacaulay_iff_ringKrullDim_le_depth]
  have hQ' : ringKrullDim R ≤ ((depth (ModuleCat.of R Q) + 1 : ℕ∞) : WithBot ℕ∞) := by
    simpa only [WithBot.coe_add, WithBot.coe_one] using hQ
  refine (le_inf hN.ringKrullDim_le_depth hQ').trans ?_
  rw [← WithBot.coe_inf]
  exact WithBot.coe_le_coe.2 (depth_min_snd_trd_add_one_le_fst_of_exact f g hfg hf hg)

end Module.IsMaximalCohenMacaulay

namespace TauCeti
section Category

variable (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R]

/-- The object property on `ModuleCat R` selecting the finite maximal Cohen–Macaulay modules. -/
def IsFiniteMaximalCohenMacaulay : ObjectProperty (ModuleCat.{v} R) :=
  fun M ↦ Module.Finite R M ∧ Module.IsMaximalCohenMacaulay R M

/-- Unfolds `TauCeti.IsFiniteMaximalCohenMacaulay`. -/
@[simp]
theorem isFiniteMaximalCohenMacaulay_iff (M : ModuleCat.{v} R) :
    IsFiniteMaximalCohenMacaulay.{v} R M ↔
      Module.Finite R M ∧ Module.IsMaximalCohenMacaulay R M := Iff.rfl

variable {R}

/-- Every zero `R`-module is a finite maximal Cohen–Macaulay module. -/
theorem isFiniteMaximalCohenMacaulay_of_isZero {M : ModuleCat.{v} R} (hM : IsZero M) :
    IsFiniteMaximalCohenMacaulay.{v} R M :=
  have := ModuleCat.subsingleton_of_isZero hM
  ⟨inferInstance, Module.isMaximalCohenMacaulay_of_subsingleton⟩

instance : (IsFiniteMaximalCohenMacaulay.{v} R).ContainsZero where
  exists_zero := ⟨ModuleCat.of R PUnit, ModuleCat.isZero_of_subsingleton _,
    isFiniteMaximalCohenMacaulay_of_isZero (ModuleCat.isZero_of_subsingleton _)⟩

instance : (IsFiniteMaximalCohenMacaulay.{v} R).IsClosedUnderIsomorphisms where
  of_iso e hX :=
    have := hX.1
    ⟨Module.Finite.equiv e.toLinearEquiv, e.toLinearEquiv.isMaximalCohenMacaulay_iff.1 hX.2⟩

/-- Over a Cohen–Macaulay local ring, every finite projective `R`-module is maximal
Cohen–Macaulay. -/
theorem isFiniteMaximalCohenMacaulay_of_projective (hR : Module.IsCohenMacaulay R R)
    (M : ModuleCat.{v} R) [Module.Finite R M] [Projective M] :
    IsFiniteMaximalCohenMacaulay.{v} R M :=
  have : Module.Projective R M := (IsProjective.iff_projective M).2 inferInstance
  ⟨inferInstance, hR.isMaximalCohenMacaulay_of_projective M⟩

/-- Finite maximal Cohen–Macaulay modules over a local ring are closed under extensions. -/
theorem IsFiniteMaximalCohenMacaulay.isExtensionClosed :
    (ExactStructure.abelian (ModuleCat.{v} R)).IsExtensionClosed
      (IsFiniteMaximalCohenMacaulay.{v} R) where
  prop_X₂ {S} hS h₁ h₃ := by
    have hSE := (ExactStructure.abelian_conflation S).1 hS
    have := h₁.1; have := h₃.1
    have hex := (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact S).1 hSE.exact
    have hsurj := (ModuleCat.epi_iff_surjective S.g).1 hSE.epi_g
    exact ⟨Module.Finite.of_exact hex hsurj,
      h₁.2.of_exact_middle hex ((ModuleCat.mono_iff_injective S.f).1 hSE.mono_f) hsurj h₃.2⟩

instance : (IsFiniteMaximalCohenMacaulay.{v} R).IsClosedUnderBinaryProducts :=
  IsFiniteMaximalCohenMacaulay.isExtensionClosed.isClosedUnderBinaryProducts

/-- Any retract of a finite maximal Cohen–Macaulay module over a Noetherian local ring is again
finite and maximal Cohen–Macaulay. -/
theorem IsFiniteMaximalCohenMacaulay.of_retract [IsNoetherianRing R] {M N : ModuleCat.{v} R}
    (r : Retract M N) (hN : IsFiniteMaximalCohenMacaulay.{v} R N) :
    IsFiniteMaximalCohenMacaulay.{v} R M := by
  have := hN.1
  have hr : Function.Surjective r.r.hom :=
    Function.LeftInverse.surjective fun x ↦ ConcreteCategory.congr_hom r.retract x
  let s : (ShortComplex.mk (Limits.kernel.ι r.r) r.r (Limits.kernel.condition r.r)).Splitting :=
    .ofExactOfSection _ (ShortComplex.exact_kernel r.r) r.i r.retract inferInstance
  have hprod := (s.isoBinaryBiproduct ≪≫ ModuleCat.biprodIsoProd _ _).toLinearEquiv
  have : Module.Finite R M := .of_surjective r.r.hom hr
  rw [isFiniteMaximalCohenMacaulay_iff, Module.isMaximalCohenMacaulay_iff_ringKrullDim_le_depth]
  refine ⟨‹_›, hN.2.ringKrullDim_le_depth.trans ?_⟩
  rw [depth_eq_of_linearEquiv hprod, depth_prod, WithBot.coe_inf]
  exact inf_le_right

/-- The additive full subcategory of finitely generated maximal Cohen–Macaulay `R`-modules. -/
abbrev MaximalCohenMacaulayModuleCat (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R] :=
  (IsFiniteMaximalCohenMacaulay.{v} R).FullSubcategory

namespace MaximalCohenMacaulayModuleCat

variable (R : Type u) [CommRing R] [IsLocalRing R] [Small.{v} R]

/-- The exact structure on finite maximal Cohen–Macaulay `R`-modules inherited from
`ModuleCat R`. -/
noncomputable def exactStructure : ExactStructure (MaximalCohenMacaulayModuleCat.{v} R) :=
  (ExactStructure.abelian (ModuleCat.{v} R)).fullSubcategory
    (IsFiniteMaximalCohenMacaulay.{v} R) IsFiniteMaximalCohenMacaulay.isExtensionClosed

/-- Conflations in `MaximalCohenMacaulayModuleCat R` are the short exact sequences in
`ModuleCat R`. -/
@[simp]
theorem exactStructure_conflation_iff (S : ShortComplex (MaximalCohenMacaulayModuleCat.{v} R)) :
    (exactStructure.{v} R).Conflation S ↔
      (S.map (IsFiniteMaximalCohenMacaulay.{v} R).ι).ShortExact := by
  rw [exactStructure, ExactStructure.fullSubcategory_conflation_iff,
    ExactStructure.abelian_conflation]

end MaximalCohenMacaulayModuleCat
end Category
end TauCeti
