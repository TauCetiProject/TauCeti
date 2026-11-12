/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Category.ModuleCat.Tower.Exact
public import TauCeti.Algebra.Category.ModuleCat.Tower.ProZero
public import Mathlib.Algebra.Category.ModuleCat.Abelian
import Mathlib.Algebra.Homology.ShortComplex.ModuleCat

/-!
# Pro-isomorphisms induce isomorphisms on inverse limits

A map of towers of modules whose kernel and cokernel are pro-zero induces an isomorphism
on inverse limits. More generally, in a levelwise exact sequence `0 → K → F → G → C`,
pro-zero error towers `K` and `C` can both be discarded when taking the limit.

The cokernel error disappears because its limit vanishes. Compatible target elements can
therefore be lifted levelwise. The kernel error disappears in two ways: its limit vanishes,
giving uniqueness, and its first derived limit vanishes, allowing the levelwise lifts to
be corrected into a compatible family. No surjectivity of the transitions is required.

This is useful in cohomology and completion comparisons: replacing a module sheaf by its
quotient by parameter-power torsion can produce pro-zero errors on both sides of the
comparison of towers. Unlike a levelwise injective comparison, a pro-isomorphism retains
these kernel errors until after taking the inverse limit.

## References

* C. A. Weibel, *An introduction to homological algebra*, §3.5, the six-term limit sequence.
* The Stacks Project, Lemma 52.3.2 (0BLD), cohomology and completion.
* The Stacks Project, Lemma 52.12.7 (0EII), algebraization of formal sections.
-/

public section

noncomputable section

namespace TauCeti.ModuleTower

open CategoryTheory Limits Opposite

universe v u

variable {R : Type u} [Ring R] {K F G C : ModuleTower.{v} R}

/-- Pro-zero kernel and cokernel errors in a levelwise exact sequence do not affect the
inverse limit. The map `K → F` must be injective, but `F → G` need not be injective or
surjective at any level, and the map `G → C` need not be surjective. -/
theorem limMap_bijective_of_exact_of_isProZero (i : K ⟶ F) (f : F ⟶ G) (g : G ⟶ C)
    (hi : ∀ n, Function.Injective (i.app (op n)).hom)
    (hif : ∀ n, Function.Exact (i.app (op n)).hom (f.app (op n)).hom)
    (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
    (hK : K.IsProZero) (hC : C.IsProZero) : Function.Bijective (limMap f) := by
  let : Subsingleton K.lim :=
    Submodule.subsingleton_iff_eq_bot.mpr (lim_eq_bot_of_isProZero hK)
  let : Subsingleton C.lim :=
    Submodule.subsingleton_iff_eq_bot.mpr (lim_eq_bot_of_isProZero hC)
  let : Subsingleton K.limOne := subsingleton_limOne_of_isProZero hK
  refine ⟨(LinearMap.injective_iff_eq_zero_of_exact (exact_limMap hi hif)).mpr ?_, fun y ↦ ?_⟩
  · apply LinearMap.ext
    intro x
    rw [Subsingleton.elim x 0, map_zero, LinearMap.zero_apply]
  -- The cokernel error vanishes, so the compatible family `y` lifts to a family `b`.
  have hy : productMap g (y : G.Product) = 0 := by
    simpa only [coe_limMap_apply, Submodule.coe_zero] using
      congrArg Subtype.val (Subsingleton.elim (limMap g y) 0)
  obtain ⟨b, hb⟩ := (exact_productMap hfg (y : G.Product)).mp hy
  exact limMap_mem_range_of_subsingleton_limOne hif y b hb

/-- A pro-isomorphism of towers, meaning a map with pro-zero kernel and cokernel, is
bijective on inverse limits. In particular, no levelwise monomorphism assumption is needed. -/
theorem limMap_bijective_of_proIsomorphism (f : F ⟶ G)
    (hf : Functor.proIsomorphisms ℕᵒᵖ (ModuleCat.{v} R) f) :
    Function.Bijective (limMap f) := by
  have hkernel (n : ℕ) := (ShortComplex.exact_kernel f).map_of_mono_of_preservesKernel
    ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj (op n)) inferInstance inferInstance
  have hcokernel (n : ℕ) := (ShortComplex.exact_cokernel f).map_of_epi_of_preservesCokernel
    ((evaluation ℕᵒᵖ (ModuleCat.{v} R)).obj (op n)) inferInstance inferInstance
  exact limMap_bijective_of_exact_of_isProZero (kernel.ι f) f (cokernel.π f)
    (fun n ↦ (ModuleCat.mono_iff_injective _).mp inferInstance)
    (fun n ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hkernel n))
    (fun n ↦ (ShortComplex.ShortExact.moduleCat_exact_iff_function_exact _).mp (hcokernel n))
    hf.1 hf.2

/-- The linear equivalence of inverse limits induced by a pro-isomorphism of towers. -/
def limEquivOfProIsomorphism (f : F ⟶ G)
    (hf : Functor.proIsomorphisms ℕᵒᵖ (ModuleCat.{v} R) f) : F.lim ≃ₗ[R] G.lim :=
  LinearEquiv.ofBijective (limMap f) (limMap_bijective_of_proIsomorphism f hf)

/-- The equivalence induced by a pro-isomorphism is the usual map on inverse limits. -/
@[simp]
theorem limEquivOfProIsomorphism_apply (f : F ⟶ G)
    (hf : Functor.proIsomorphisms ℕᵒᵖ (ModuleCat.{v} R) f) (x : F.lim) :
    limEquivOfProIsomorphism f hf x = limMap f x :=
  (rfl)

/-- Applying the limit map to the inverse equivalence recovers the target element. -/
@[simp]
theorem limMap_limEquivOfProIsomorphism_symm_apply (f : F ⟶ G)
    (hf : Functor.proIsomorphisms ℕᵒᵖ (ModuleCat.{v} R) f) (y : G.lim) :
    limMap f ((limEquivOfProIsomorphism f hf).symm y) = y :=
  (limEquivOfProIsomorphism f hf).apply_symm_apply y

/-- The inverse equivalence lifts every target component through the original map. -/
@[simp]
theorem app_coe_limEquivOfProIsomorphism_symm (f : F ⟶ G)
    (hf : Functor.proIsomorphisms ℕᵒᵖ (ModuleCat.{v} R) f) (y : G.lim) (n : ℕ) :
    (f.app (op n)).hom (((limEquivOfProIsomorphism f hf).symm y : F.Product) n) =
      (y : G.Product) n := by
  have h := congrArg (fun x : G.lim ↦ (x : G.Product) n)
    (limMap_limEquivOfProIsomorphism_symm_apply f hf y)
  simpa only [coe_limMap_apply, productMap_apply] using h

end TauCeti.ModuleTower
