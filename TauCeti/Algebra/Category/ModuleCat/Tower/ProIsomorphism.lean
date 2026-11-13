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
on inverse limits. More generally, in a levelwise exact sequence `K → F → G → C`,
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

/-- Pro-zero error towers in a levelwise exact sequence `K → F → G → C` do not affect
the inverse limit. No levelwise injectivity or surjectivity assumptions are needed. -/
theorem limMap_bijective_of_exact_of_isProZero (i : K ⟶ F) (f : F ⟶ G) (g : G ⟶ C)
    (hif : ∀ n, Function.Exact (i.app (op n)).hom (f.app (op n)).hom)
    (hfg : ∀ n, Function.Exact (f.app (op n)).hom (g.app (op n)).hom)
    (hK : K.IsProZero) (hC : C.IsProZero) : Function.Bijective (limMap f) := by
  let : Subsingleton C.lim :=
    Submodule.subsingleton_iff_eq_bot.mpr (lim_eq_bot_of_isProZero hC)
  let : Subsingleton K.limOne := subsingleton_limOne_of_isProZero hK
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦ ?_⟩
  · -- Every component lifts from `K` at a later level whose transition kills it.
    apply Subtype.ext
    funext n
    obtain ⟨m, hnm, hm⟩ := K.isProZero_iff_exists_transitionOfLE_eq_zero.mp hK n
    have hxm : (f.app (op m)).hom ((x : F.Product) m) = 0 := by
      simpa only [coe_limMap_apply, productMap_apply, Submodule.coe_zero, Pi.zero_apply] using
        congrArg (fun y : G.lim ↦ (y : G.Product) m) hx
    obtain ⟨z, hz⟩ := (hif m _).mp hxm
    rw [Submodule.coe_zero, Pi.zero_apply, ← F.transitionOfLE_coe_lim x hnm, ← hz,
      ← LinearMap.comp_apply, ← app_comp_transitionOfLE, LinearMap.comp_apply, hm,
      LinearMap.zero_apply, map_zero]
  -- The cokernel error vanishes, so the compatible family `y` lifts to a family `b`.
  have hy : productMap g (y : G.Product) = 0 := by
    simpa only [coe_limMap_apply, Submodule.coe_zero] using
      congrArg Subtype.val (Subsingleton.elim (limMap g y) 0)
  obtain ⟨b, hb⟩ := (exact_productMap hfg (y : G.Product)).mp hy
  exact mem_range_limMap_of_subsingleton_limOne hif y b hb

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

/-- Applying the inverse equivalence to the limit map recovers the source element. -/
@[simp]
theorem limEquivOfProIsomorphism_symm_limMap_apply (f : F ⟶ G)
    (hf : Functor.proIsomorphisms ℕᵒᵖ (ModuleCat.{v} R) f) (x : F.lim) :
    (limEquivOfProIsomorphism f hf).symm (limMap f x) = x :=
  (limEquivOfProIsomorphism f hf).symm_apply_apply x

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
