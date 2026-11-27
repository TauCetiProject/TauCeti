/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Geometry.Manifold.Algebra.Monoid
public import Mathlib.Geometry.Manifold.ContMDiffMap

/-!
# Products of smooth functions on a product manifold

For `C^n` maps `f` on `M` and `g` on `N` into a manifold `G` with `C^n` multiplication, the map
`(x, y) ↦ f x * g y` on `M × N` is `C^n` (`ContMDiffMap.mulProd`). When `G` has a zero absorbing
multiplication, its closed support lies in the product of the closed supports of `f` and `g`
(`ContMDiffMap.tsupport_mulProd_subset`). For `C^n` maps `f : M → M'` and `g : N → N'`, the
product map `(x, y) ↦ (f x, g y)` is `C^n` (`ContMDiffMap.prodMap`).
-/

public section

open Function Set
open scoped Manifold

namespace ContMDiffMap

variable {𝕜 : Type*} [NontriviallyNormedField 𝕜]
  {E H : Type*} [NormedAddCommGroup E] [NormedSpace 𝕜 E] [TopologicalSpace H]
  {I : ModelWithCorners 𝕜 E H} {M : Type*} [TopologicalSpace M] [ChartedSpace H M]
  {E' H' : Type*} [NormedAddCommGroup E'] [NormedSpace 𝕜 E'] [TopologicalSpace H']
  {J : ModelWithCorners 𝕜 E' H'} {N : Type*} [TopologicalSpace N] [ChartedSpace H' N]
  {F K : Type*} [NormedAddCommGroup F] [NormedSpace 𝕜 F] [TopologicalSpace K]
  {I' : ModelWithCorners 𝕜 F K} {G : Type*} [TopologicalSpace G] [ChartedSpace K G]
  {n : WithTop ℕ∞}

section ProdMap

variable {F' K' : Type*} [NormedAddCommGroup F'] [NormedSpace 𝕜 F'] [TopologicalSpace K']
  {J' : ModelWithCorners 𝕜 F' K'} {N' : Type*} [TopologicalSpace N'] [ChartedSpace K' N']

/-- The `C^n` map `(x, y) ↦ (f x, g y)` on `M × N`, for `C^n` maps `f` on `M` and `g` on `N`. -/
def prodMap (f : C^n⟮I, M; I', G⟯) (g : C^n⟮J, N; J', N'⟯) :
    C^n⟮I.prod J, M × N; I'.prod J', G × N'⟯ :=
  ⟨Prod.map f g, f.contMDiff.prodMap g.contMDiff⟩

@[simp]
theorem coe_prodMap (f : C^n⟮I, M; I', G⟯) (g : C^n⟮J, N; J', N'⟯) :
    ⇑(f.prodMap g) = Prod.map f g :=
  (rfl)

@[simp]
theorem prodMap_apply (f : C^n⟮I, M; I', G⟯) (g : C^n⟮J, N; J', N'⟯) (z : M × N) :
    f.prodMap g z = (f z.1, g z.2) :=
  (rfl)

end ProdMap

section Mul

variable [Mul G] [ContMDiffMul I' n G]

/-- The `C^n` map `(x, y) ↦ f x * g y` on `M × N`, for `C^n` maps `f` on `M` and `g` on `N`. -/
def mulProd (f : C^n⟮I, M; I', G⟯) (g : C^n⟮J, N; I', G⟯) : C^n⟮I.prod J, M × N; I', G⟯ :=
  ⟨fun z ↦ f z.1 * g z.2, (f.contMDiff.comp contMDiff_fst).mul (g.contMDiff.comp contMDiff_snd)⟩

@[simp]
theorem mulProd_apply (f : C^n⟮I, M; I', G⟯) (g : C^n⟮J, N; I', G⟯) (z : M × N) :
    f.mulProd g z = f z.1 * g z.2 :=
  (rfl)

end Mul

variable [MulZeroClass G] [ContMDiffMul I' n G]

/-- The support of `(x, y) ↦ f x * g y` lies in the product of the supports of `f` and `g`. -/
theorem support_mulProd_subset (f : C^n⟮I, M; I', G⟯) (g : C^n⟮J, N; I', G⟯) :
    support (f.mulProd g) ⊆ support f ×ˢ support g :=
  fun _ hz ↦ ⟨left_ne_zero_of_mul hz, right_ne_zero_of_mul hz⟩

/-- The closed support of `(x, y) ↦ f x * g y` lies in the product of the closed supports of `f`
and `g`. -/
theorem tsupport_mulProd_subset (f : C^n⟮I, M; I', G⟯) (g : C^n⟮J, N; I', G⟯) :
    tsupport (f.mulProd g) ⊆ tsupport f ×ˢ tsupport g := by
  rw [tsupport, tsupport, tsupport, ← closure_prod_eq]
  exact closure_mono (support_mulProd_subset f g)

end ContMDiffMap
