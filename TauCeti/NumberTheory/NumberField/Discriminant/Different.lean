/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.NumberTheory.NumberField.Discriminant.Different

/-!
# Principal differents of disjoint composita

Transitivity and coprime base change (Neukirch, *Algebraic Number Theory*, Chapter III §2)
combine to give a generator for the different of a compositum.
-/

public section

open NumberField
open scoped NumberField

namespace TauCeti

/-- For linearly disjoint fields whose differents become coprime in their compositum,
the product of the images of the different generators generates the absolute different. -/
theorem differentIdeal_eq_span_mul_of_linearDisjoint
    {E : Type*} [Field E] [NumberField E] {F K : IntermediateField ℚ E}
    (hld : F.LinearDisjoint K) (hsup : F ⊔ K = ⊤) {a : 𝓞 F} {b : 𝓞 K}
    (ha : differentIdeal ℤ (𝓞 F) = Ideal.span {a})
    (hb : differentIdeal ℤ (𝓞 K) = Ideal.span {b})
    (hcop : IsCoprime (algebraMap (𝓞 F) (𝓞 E) a) (algebraMap (𝓞 K) (𝓞 E) b)) :
    differentIdeal ℤ (𝓞 E) = Ideal.span
      {algebraMap (𝓞 F) (𝓞 E) a * algebraMap (𝓞 K) (𝓞 E) b} := by
  let : Algebra (FractionRing (𝓞 F)) (FractionRing (𝓞 E)) := FractionRing.liftAlgebra _ _
  have hcop' : IsCoprime ((differentIdeal ℤ (𝓞 K)).map (algebraMap (𝓞 K) (𝓞 E)))
      ((differentIdeal ℤ (𝓞 F)).map (algebraMap (𝓞 F) (𝓞 E))) := by
    simpa only [ha, hb, Ideal.map_span, Set.image_singleton, Ideal.isCoprime_span_singleton_iff]
      using hcop.symm
  have hrel := IsDedekindDomain.differentIdeal_eq_map_differentIdeal ℤ (𝓞 E)
    (𝓞 K) (𝓞 F) (F₁ := K) (F₂ := F) hld.symm (by simpa only [sup_comm] using hsup) hcop'
  rw [differentIdeal_eq_differentIdeal_mul_differentIdeal ℤ (𝓞 K) (𝓞 E), hrel, ha, hb]
  simp only [Ideal.map_span, Set.image_singleton, Ideal.span_singleton_mul_span_singleton]

end TauCeti
