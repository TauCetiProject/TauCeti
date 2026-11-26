/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.InnerProductSpace.ProdL2
public import TauCeti.Analysis.InnerProductSpace.HilbertBasis.Basic

/-!
# Products of Hilbert bases

Given Hilbert bases `b` of `E` and `c` of `F`, their orthogonal direct sum `b.prodLp c` is a
Hilbert basis of the `L²` product `WithLp 2 (E × F)` indexed by `ι ⊕ κ`. This is the
Hilbert-basis counterpart of `OrthonormalBasis.prod` (named `prodLp` to distinguish it from
`HilbertBasis.prod` on `L²(μ ⊗ ν)`).
-/

public section

open scoped InnerProductSpace

variable {ι κ 𝕜 E F : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E]
  [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]

namespace HilbertBasis

/-- The Hilbert basis of the `L²` product `WithLp 2 (E × F)` formed from Hilbert bases of `E` and
`F`. -/
protected noncomputable def prodLp (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) :
    HilbertBasis (ι ⊕ κ) 𝕜 (WithLp 2 (E × F)) :=
  haveI : CompleteSpace E := b.completeSpace
  haveI : CompleteSpace F := c.completeSpace
  HilbertBasis.mkOfOrthogonalEqBot
    (v := Sum.elim (fun i ↦ WithLp.toLp 2 (b i, (0 : F)))
      (fun j ↦ WithLp.toLp 2 ((0 : E), c j)))
    (by
      classical
      rw [orthonormal_iff_ite]
      rintro (i | j) (i' | j')
      · simp [WithLp.prod_inner_apply, orthonormal_iff_ite.1 b.orthonormal]
      · simp [WithLp.prod_inner_apply]
      · simp [WithLp.prod_inner_apply]
      · simp [WithLp.prod_inner_apply, orthonormal_iff_ite.1 c.orthonormal])
    (by
      rw [Submodule.eq_bot_iff]
      intro x hx
      rw [Submodule.mem_orthogonal] at hx
      apply (WithLp.linearEquiv 2 𝕜 (E × F)).injective
      rw [map_zero, WithLp.coe_linearEquiv]
      refine Prod.ext ?_ ?_
      · exact b.repr.map_eq_zero_iff.1 <| lp.ext <| funext fun i ↦ by
          simpa [b.repr_apply_apply, WithLp.prod_inner_apply] using
            hx _ (Submodule.subset_span ⟨Sum.inl i, rfl⟩)
      · exact c.repr.map_eq_zero_iff.1 <| lp.ext <| funext fun j ↦ by
          simpa [c.repr_apply_apply, WithLp.prod_inner_apply] using
            hx _ (Submodule.subset_span ⟨Sum.inr j, rfl⟩))

/-- The left basis vectors of `b.prodLp c` are `(b i, 0)`. -/
@[simp]
theorem prodLp_apply_inl (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (i : ι) :
    b.prodLp c (Sum.inl i) = WithLp.toLp 2 (b i, (0 : F)) := by
  have : CompleteSpace E := b.completeSpace
  have : CompleteSpace F := c.completeSpace
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) (Sum.inl i)

/-- The right basis vectors of `b.prodLp c` are `(0, c j)`. -/
@[simp]
theorem prodLp_apply_inr (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F) (j : κ) :
    b.prodLp c (Sum.inr j) = WithLp.toLp 2 ((0 : E), c j) := by
  have : CompleteSpace E := b.completeSpace
  have : CompleteSpace F := c.completeSpace
  exact congrFun (HilbertBasis.coe_mkOfOrthogonalEqBot _ _) (Sum.inr j)

/-- Coordinates of `x` in `b.prodLp c` on the left summand agree with `b.repr` on the first
component. -/
@[simp]
theorem repr_prodLp_inl (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (x : WithLp 2 (E × F)) (i : ι) :
    (b.prodLp c).repr x (Sum.inl i) = b.repr (WithLp.ofLp x).1 i := by
  rw [(b.prodLp c).repr_apply_apply, b.repr_apply_apply, prodLp_apply_inl, WithLp.prod_inner_apply]
  simp

/-- Coordinates of `x` in `b.prodLp c` on the right summand agree with `c.repr` on the second
component. -/
@[simp]
theorem repr_prodLp_inr (b : HilbertBasis ι 𝕜 E) (c : HilbertBasis κ 𝕜 F)
    (x : WithLp 2 (E × F)) (j : κ) :
    (b.prodLp c).repr x (Sum.inr j) = c.repr (WithLp.ofLp x).2 j := by
  rw [(b.prodLp c).repr_apply_apply, c.repr_apply_apply, prodLp_apply_inr, WithLp.prod_inner_apply]
  simp

/-- On finite index types, `HilbertBasis.prodLp` agrees with `OrthonormalBasis.prod`. -/
@[simp]
theorem toOrthonormalBasis_prodLp [Fintype ι] [Fintype κ] (b : HilbertBasis ι 𝕜 E)
    (c : HilbertBasis κ 𝕜 F) :
    (b.prodLp c).toOrthonormalBasis = b.toOrthonormalBasis.prod c.toOrthonormalBasis :=
  DFunLike.ext _ _ fun i ↦ by rcases i with i | j <;> simp

end HilbertBasis
