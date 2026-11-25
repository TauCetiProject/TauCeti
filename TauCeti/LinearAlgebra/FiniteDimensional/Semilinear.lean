/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FiniteDimensional.Basic

/-!
# Injective semilinear endomorphisms of finite-dimensional spaces

An injective linear endomorphism of a finite-dimensional vector space is surjective
(`LinearMap.surjective_of_injective`). The same holds for an endomorphism that is semilinear with
respect to a surjective ring endomorphism `σ` of the scalars: such a map carries a basis to a
linearly independent family, so its range has full dimension. The main example is the Frobenius
of an isocrystal, which is semilinear with respect to an automorphism of the coefficient field.
-/

public section

namespace LinearMap

variable {K V : Type*} [DivisionRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V]
  {σ : K →+* K} [RingHomSurjective σ]

/-- An injective endomorphism of a finite-dimensional vector space that is semilinear with
respect to a surjective ring endomorphism of the scalars is surjective. -/
theorem surjective_of_injectiveₛₗ {f : V →ₛₗ[σ] V} (hf : Function.Injective f) :
    Function.Surjective f := by
  have hσ : Function.Bijective σ := ⟨σ.injective, RingHomSurjective.is_surjective⟩
  have hrank : Module.rank K V = Module.rank K (range f) :=
    rank_eq_of_equiv_equiv σ
      (AddEquiv.ofBijective f.rangeRestrict.toAddMonoidHom
        ⟨fun x y h => hf (congrArg Subtype.val h), f.surjective_rangeRestrict⟩)
      hσ fun r x => Subtype.ext (map_smulₛₗ f r x)
  rw [← range_eq_top]
  exact Submodule.eq_top_of_finrank_eq (congrArg Cardinal.toNat hrank).symm

end LinearMap
