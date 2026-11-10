/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Line
public import TauCeti.LinearAlgebra.Determinant.Exact
public import TauCeti.LinearAlgebra.Prod
public import TauCeti.LinearAlgebra.Exact
import TauCeti.Algebra.Module.Equiv.Basic
import TauCeti.LinearAlgebra.Dual.Contraction
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The determinant line of a direct sum

For linear maps `f : M → N` and `g : M' → N'` between vector spaces whose kernels and cokernels
are finite-dimensional, the direct sum `f ⊕ g = f.prodMap g : M × M' → N × N'` has kernel
`ker f × ker g` and cokernel `coker f × coker g`. The short exact sequences

`0 → ker f → ker (f ⊕ g) → ker g → 0` and `0 → coker f → coker (f ⊕ g) → coker g → 0`,

with the inclusions `x ↦ (x, 0)` first and the second projections last
(`LinearMap.exact_kerInlProdMap_kerSndProdMap` and
`LinearMap.exact_cokerInlProdMap_cokerSndProdMap` in `TauCeti.LinearAlgebra.Exact`), identify the
determinant lines `det (f ⊕ g) = det (ker (f ⊕ g)) ⊗ (det (coker (f ⊕ g)))^*` with
`(det (ker f) ⊗ det (ker g)) ⊗ ((det (coker f))^* ⊗ (det (coker g))^*)`. Moving `(det (coker f))^*`
past `det (ker g)` gives the canonical isomorphism

`det (f ⊕ g) ≃ det f ⊗ det g`

(`LinearMap.detLineProdMapEquiv`), for the determinant lines
`det f = det (ker f) ⊗ (det (coker f))^*` of `LinearMap.detLine`. No bases or complements are
chosen.

The isomorphism carries the Koszul sign `(-1) ^ (dim (coker f) * dim (ker g))` of that move. This
is the sign rule for determinant lines as graded lines, in which `det (ker f)` sits in degree
`dim (ker f)` and `(det (coker f))^*` in degree `-dim (coker f)`, so that `det f` sits in degree
the index of `f`. With this sign, exchanging the two summands is the exchange of the two tensor
factors up to the sign `(-1) ^ (ind f * ind g)` of the product of the indices
(`LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`); the parity of `dim (ker f) + dim (coker f)`
is that of the index. Without the Koszul sign the exchange law would instead carry
`(-1) ^ (dim (ker f) * dim (ker g) + dim (coker f) * dim (coker g))`, which is not a function of
the indices.

For Fredholm operators this is the direct-sum law of determinant lines: it orients the
determinant line of a direct sum of operators from orientations of the summands, as for the
disjoint union of two linearized problems before they are glued.

## Main declarations

* `LinearMap.detLineProdMapEquiv`: the isomorphism `det (f ⊕ g) ≃ det f ⊗ det g`.
* `LinearMap.detLineProdMapEquiv_tmul`: its value on exterior products.
* `LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`: exchanging the summands exchanges the
  tensor factors up to the sign `(-1) ^ (ind f * ind g)`.

## References

* F. Knudsen and D. Mumford, *The projectivity of the moduli space of stable curves I:
  Preliminaries on "det" and "Div"*, Math. Scand. **39** (1976), 19–55 (determinants as graded
  lines and the Koszul sign rule).
* A. Zinger, *The determinant line bundle for Fredholm operators: construction, properties,
  and classification*, Math. Scand. **118** (2016), 203–268, arXiv:1304.6368 (the direct-sum
  isomorphism of determinant lines and its exchange sign).
-/

public section

noncomputable section

open Module TensorProduct

namespace LinearMap

/-! ### The determinant line of a direct sum -/

variable {K : Type*} [Field K] {M N M' N' : Type*} [AddCommGroup M] [Module K M]
  [AddCommGroup N] [Module K N] [AddCommGroup M'] [Module K M'] [AddCommGroup N'] [Module K N']
  (f : M →ₗ[K] N) (g : M' →ₗ[K] N')

variable [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)]
  [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (N' ⧸ range g)]

/-- **The determinant line of a direct sum.** For linear maps `f` and `g` with finite-dimensional
kernels and cokernels, the canonical isomorphism `det (f ⊕ g) ≃ det f ⊗ det g` for the direct sum
`f ⊕ g = f.prodMap g`. It splits the kernel and the cokernel of `f ⊕ g` along the short exact
sequences `0 → ker f → ker (f ⊕ g) → ker g → 0` and `0 → coker f → coker (f ⊕ g) → coker g → 0`
(`TauCeti.detLineShortExactEquiv`), regroups the four factors, and multiplies by the Koszul sign
`(-1) ^ (dim (coker f) * dim (ker g))` of moving `(det (coker f))^*` past `det (ker g)`. Its value
on exterior products is `LinearMap.detLineProdMapEquiv_tmul`. -/
def detLineProdMapEquiv : (f.prodMap g).detLine ≃ₗ[K] f.detLine ⊗[K] g.detLine :=
  TensorProduct.congr
      (TauCeti.detLineShortExactEquiv (kerInlProdMap_injective f g)
        (exact_kerInlProdMap_kerSndProdMap f g) (kerSndProdMap_surjective f g)).symm
      ((TauCeti.detLineShortExactEquiv (cokerInlProdMap_injective f g)
          (exact_cokerInlProdMap_cokerSndProdMap f g) (cokerSndProdMap_surjective f g)).dualMap ≪≫ₗ
        (dualDistribEquiv K _ _).symm) ≪≫ₗ
    TensorProduct.tensorTensorTensorComm K _ _ _ _ ≪≫ₗ
    LinearEquiv.smulOfUnit ((-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g)))

omit [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (N' ⧸ range g)] in
/-- The kernel sequence joins the exterior products of `u` and `w` into that of the images of `u`
followed by those of `w`. -/
private theorem coe_detLineShortExactEquiv_ker_tmul (u : Fin (finrank K (ker f)) → ker f)
    (w : Fin (finrank K (ker g)) → ker g) :
    (TauCeti.detLineShortExactEquiv (kerInlProdMap_injective f g)
        (exact_kerInlProdMap_kerSndProdMap f g) (kerSndProdMap_surjective f g)
        (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ w) :
        ExteriorAlgebra K (ker (f.prodMap g))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (kerInlProdMap f g ∘ u) (kerInrProdMap f g ∘ w)) :=
  TauCeti.coe_detLineShortExactEquiv_tmul_of_comp_eq_id _ _ _
    (kerSndProdMap_comp_kerInrProdMap f g) u w

omit [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)] in
/-- The cokernel sequence joins the exterior products of `x` and `y` into that of the images of
`x` followed by those of `y`. -/
private theorem coe_detLineShortExactEquiv_coker_tmul
    (x : Fin (finrank K (N ⧸ range f)) → N ⧸ range f)
    (y : Fin (finrank K (N' ⧸ range g)) → N' ⧸ range g) :
    (TauCeti.detLineShortExactEquiv (cokerInlProdMap_injective f g)
        (exact_cokerInlProdMap_cokerSndProdMap f g) (cokerSndProdMap_surjective f g)
        (exteriorPower.ιMulti K _ x ⊗ₜ exteriorPower.ιMulti K _ y) :
        ExteriorAlgebra K ((N × N') ⧸ range (f.prodMap g))) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (cokerInlProdMap f g ∘ x) (cokerInrProdMap f g ∘ y)) :=
  TauCeti.coe_detLineShortExactEquiv_tmul_of_comp_eq_id _ _ _
    (cokerSndProdMap_comp_cokerInrProdMap f g) x y

/-- **The value of `LinearMap.detLineProdMapEquiv` on exterior products.** Let `u`, `w`, `x` and
`y` be families of `dim (ker f)`, `dim (ker g)`, `dim (coker f)` and `dim (coker g)` vectors of
`ker f`, `ker g`, `coker f` and `coker g`. Let `β` be the exterior product in `ker (f ⊕ g)` of
the images of `u` followed by those of `w`, and `ε` that in `coker (f ⊕ g)` of the images of `x`
followed by those of `y`. If `ψ` and `χ` take the value `1` at the exterior products of `x` and of
`y`, then the isomorphism sends `β ⊗ φ` to
`((-1) ^ (dim (coker f) * dim (ker g)) * φ ε) • ((α ⊗ ψ) ⊗ (γ ⊗ χ))`, with `α` and `γ` the
exterior products of `u` and `w`. -/
theorem detLineProdMapEquiv_tmul (u : Fin (finrank K (ker f)) → ker f)
    (w : Fin (finrank K (ker g)) → ker g) (x : Fin (finrank K (N ⧸ range f)) → N ⧸ range f)
    (y : Fin (finrank K (N' ⧸ range g)) → N' ⧸ range g)
    {β : TauCeti.detLine K (ker (f.prodMap g))} (hβ : (β : ExteriorAlgebra K (ker (f.prodMap g))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (kerInlProdMap f g ∘ u) (kerInrProdMap f g ∘ w)))
    {ε : TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g))}
    (hε : (ε : ExteriorAlgebra K ((N × N') ⧸ range (f.prodMap g))) =
      ExteriorAlgebra.ιMulti K _ (Fin.append (cokerInlProdMap f g ∘ x) (cokerInrProdMap f g ∘ y)))
    (φ : Dual K (TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g))))
    {ψ : Dual K (TauCeti.detLine K (N ⧸ range f))} (hψ : ψ (exteriorPower.ιMulti K _ x) = 1)
    {χ : Dual K (TauCeti.detLine K (N' ⧸ range g))} (hχ : χ (exteriorPower.ιMulti K _ y) = 1) :
    detLineProdMapEquiv f g (β ⊗ₜ φ) =
      ((-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) * φ ε) •
        ((exteriorPower.ιMulti K _ u ⊗ₜ ψ) ⊗ₜ (exteriorPower.ιMulti K _ w ⊗ₜ χ)) := by
  -- Split `β` along `0 → ker f → ker (f ⊕ g) → ker g → 0`.
  have hβ' : (TauCeti.detLineShortExactEquiv (kerInlProdMap_injective f g)
      (exact_kerInlProdMap_kerSndProdMap f g) (kerSndProdMap_surjective f g)).symm β =
      exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ w := by
    rw [LinearEquiv.symm_apply_eq]
    exact Subtype.ext (by rw [hβ, coe_detLineShortExactEquiv_ker_tmul])
  -- Join `ε` along `0 → coker f → coker (f ⊕ g) → coker g → 0`.
  have hε' : TauCeti.detLineShortExactEquiv (cokerInlProdMap_injective f g)
      (exact_cokerInlProdMap_cokerSndProdMap f g) (cokerSndProdMap_surjective f g)
      (exteriorPower.ιMulti K _ x ⊗ₜ exteriorPower.ιMulti K _ y) = ε :=
    Subtype.ext (by rw [hε, coe_detLineShortExactEquiv_coker_tmul])
  -- The functional on `det (coker f) ⊗ det (coker g)` is `φ ε • (ψ ⊗ χ)`.
  have hdual : (dualDistribEquiv K _ _).symm
      ((TauCeti.detLineShortExactEquiv (cokerInlProdMap_injective f g)
        (exact_cokerInlProdMap_cokerSndProdMap f g) (cokerSndProdMap_surjective f g)).dualMap φ) =
      φ ε • (ψ ⊗ₜ χ) := by
    rw [LinearEquiv.symm_apply_eq, map_smul]
    refine TensorProduct.ext' fun a b ↦ ?_
    rw [← TauCeti.apply_smul_eq_self_of_finrank_eq_one (TauCeti.finrank_detLine K _) hψ a,
      ← TauCeti.apply_smul_eq_self_of_finrank_eq_one (TauCeti.finrank_detLine K _) hχ b]
    simp only [TensorProduct.smul_tmul_smul, map_smul, LinearEquiv.dualMap_apply, hε',
      LinearMap.smul_apply, dualDistribEquiv_tmul_tmul, hψ, hχ, smul_eq_mul]
    ring
  simp only [detLineProdMapEquiv, LinearEquiv.trans_apply, TensorProduct.congr_tmul, hβ',
    hdual, TensorProduct.tmul_smul, map_smul, TensorProduct.tensorTensorTensorComm_tmul]
  simp only [LinearEquiv.smulOfUnit_apply, Units.val_pow_eq_pow_val, Units.val_neg, Units.val_one]
  rw [smul_comm, smul_smul]

/-! ### Exchanging the summands -/

omit [FiniteDimensional K (N ⧸ range f)] [FiniteDimensional K (N' ⧸ range g)] in
/-- An isomorphism `ker (f ⊕ g) ≃ ker (g ⊕ f)` exchanging the coordinates moves the exterior
product of the images of `u` followed by those of `w` to that of the images of `w` followed by
those of `u`, up to the sign `(-1) ^ (dim (ker g) * dim (ker f))`. -/
private theorem detLineCongr_detLineShortExactEquiv_ker_tmul
    (e : ker (f.prodMap g) ≃ₗ[K] ker (g.prodMap f)) (he : ∀ z, (e z : M' × M) = (z : M × M').swap)
    (u : Fin (finrank K (ker f)) → ker f) (w : Fin (finrank K (ker g)) → ker g) :
    LinearEquiv.detLineCongr e (TauCeti.detLineShortExactEquiv (kerInlProdMap_injective f g)
        (exact_kerInlProdMap_kerSndProdMap f g) (kerSndProdMap_surjective f g)
        (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ w)) =
      (-1 : K) ^ (finrank K (ker g) * finrank K (ker f)) •
        TauCeti.detLineShortExactEquiv (kerInlProdMap_injective g f)
          (exact_kerInlProdMap_kerSndProdMap g f) (kerSndProdMap_surjective g f)
          (exteriorPower.ιMulti K _ w ⊗ₜ exteriorPower.ιMulti K _ u) := by
  have hu : ⇑e.toLinearMap ∘ kerInlProdMap f g ∘ u = kerInrProdMap g f ∘ u :=
    funext fun i ↦ Subtype.ext (by simp [he])
  have hw : ⇑e.toLinearMap ∘ kerInrProdMap f g ∘ w = kerInlProdMap g f ∘ w :=
    funext fun i ↦ Subtype.ext (by simp [he])
  refine Subtype.ext ?_
  rw [LinearEquiv.coe_detLineCongr, coe_detLineShortExactEquiv_ker_tmul,
    TauCeti.ExteriorAlgebra.map_ιMulti_append, hu, hw, Submodule.coe_smul,
    coe_detLineShortExactEquiv_ker_tmul]

omit [FiniteDimensional K (ker f)] [FiniteDimensional K (ker g)] in
/-- An isomorphism `coker (f ⊕ g) ≃ coker (g ⊕ f)` exchanging the coordinates pulls the exterior
product of the images of `y` followed by those of `x` back to that of the images of `x` followed
by those of `y`, up to the sign `(-1) ^ (dim (coker f) * dim (coker g))`. -/
private theorem detLineCongr_symm_detLineShortExactEquiv_coker_tmul
    (Q : ((N × N') ⧸ range (f.prodMap g)) ≃ₗ[K] ((N' × N) ⧸ range (g.prodMap f)))
    (hQ : ∀ z, Q (Submodule.Quotient.mk z) = Submodule.Quotient.mk z.swap)
    (x : Fin (finrank K (N ⧸ range f)) → N ⧸ range f)
    (y : Fin (finrank K (N' ⧸ range g)) → N' ⧸ range g) :
    (LinearEquiv.detLineCongr Q).symm (TauCeti.detLineShortExactEquiv
        (cokerInlProdMap_injective g f) (exact_cokerInlProdMap_cokerSndProdMap g f)
        (cokerSndProdMap_surjective g f)
        (exteriorPower.ιMulti K _ y ⊗ₜ exteriorPower.ιMulti K _ x)) =
      (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (N' ⧸ range g)) •
        TauCeti.detLineShortExactEquiv (cokerInlProdMap_injective f g)
          (exact_cokerInlProdMap_cokerSndProdMap f g) (cokerSndProdMap_surjective f g)
          (exteriorPower.ιMulti K _ x ⊗ₜ exteriorPower.ιMulti K _ y) := by
  have hQ' : ∀ z, Q.symm (Submodule.Quotient.mk z) = Submodule.Quotient.mk z.swap := fun z ↦ by
    rw [LinearEquiv.symm_apply_eq, hQ, Prod.swap_swap]
  have hy : ⇑Q.symm.toLinearMap ∘ cokerInlProdMap g f ∘ y = cokerInrProdMap f g ∘ y :=
    funext fun i ↦ by
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (y i)
      simp [← ha, hQ']
  have hx : ⇑Q.symm.toLinearMap ∘ cokerInrProdMap g f ∘ x = cokerInlProdMap f g ∘ x :=
    funext fun i ↦ by
      obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (x i)
      simp [← ha, hQ']
  refine Subtype.ext ?_
  rw [LinearEquiv.detLineCongr_symm, LinearEquiv.coe_detLineCongr,
    coe_detLineShortExactEquiv_coker_tmul, TauCeti.ExteriorAlgebra.map_ιMulti_append, hy, hx,
    Submodule.coe_smul, coe_detLineShortExactEquiv_coker_tmul]

variable (K) in
/-- A functional on the determinant line of a finite-dimensional space taking the value `1` at
the exterior product of `Module.finBasis`. -/
private theorem exists_dual_detLine_ιMulti_finBasis_eq_one (V : Type*) [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] :
    ∃ ψ : Dual K (TauCeti.detLine K V), ψ (exteriorPower.ιMulti K _ (Module.finBasis K V)) = 1 :=
  Module.Projective.exists_dual_eq_one K
    ((exteriorPower.ιMulti_ne_zero_iff _).2 (Module.finBasis K V).linearIndependent)

/-- The exchange law of `LinearMap.detLineProdMapEquiv` at the joined exterior product of
families `u` and `w` in the kernels, computed through `LinearMap.detLineProdMapEquiv_tmul` with
functionals normalized on exterior products of bases of the cokernels. -/
private theorem detLineProdMapEquiv_detLineCongr_prodComm_tmul
    (u : Fin (finrank K (ker f)) → ker f) (w : Fin (finrank K (ker g)) → ker g)
    (φ : Dual K (TauCeti.detLine K ((N × N') ⧸ range (f.prodMap g)))) :
    detLineProdMapEquiv g f ((f.prodMap g).detLineCongr (LinearEquiv.prodComm K M M')
      (LinearEquiv.prodComm K N N') (prodMap_comp_prodComm f g)
        (TauCeti.detLineShortExactEquiv (kerInlProdMap_injective f g)
          (exact_kerInlProdMap_kerSndProdMap f g) (kerSndProdMap_surjective f g)
          (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ w) ⊗ₜ φ)) =
      (-1 : K) ^ ((finrank K (ker f) + finrank K (N ⧸ range f)) *
          (finrank K (ker g) + finrank K (N' ⧸ range g))) •
        TensorProduct.comm K _ _ (detLineProdMapEquiv f g
          (TauCeti.detLineShortExactEquiv (kerInlProdMap_injective f g)
            (exact_kerInlProdMap_kerSndProdMap f g) (kerSndProdMap_surjective f g)
            (exteriorPower.ιMulti K _ u ⊗ₜ exteriorPower.ιMulti K _ w) ⊗ₜ φ)) := by
  -- Functionals taking the value `1` on exterior products of bases of the cokernels.
  obtain ⟨ψ, hψ⟩ := exists_dual_detLine_ιMulti_finBasis_eq_one K (N ⧸ range f)
  obtain ⟨χ, hχ⟩ := exists_dual_detLine_ιMulti_finBasis_eq_one K (N' ⧸ range g)
  have he : ∀ z : ker (f.prodMap g), ((LinearEquiv.prodComm K M M').ofSubmodules _ _
      (f.prodMap g |>.map_ker_eq_ker_of_comp_eq (LinearEquiv.prodComm K M M').surjective
        (LinearEquiv.prodComm K N N').injective (prodMap_comp_prodComm f g)) z : M' × M) =
      (z : M × M').swap := fun _ ↦ by simp
  have hQ : ∀ z : N × N', Submodule.Quotient.equiv (range (f.prodMap g)) (range (g.prodMap f))
      (LinearEquiv.prodComm K N N') (f.prodMap g |>.map_range_eq_range_of_comp_eq
        (LinearEquiv.prodComm K M M').surjective (prodMap_comp_prodComm f g))
        (Submodule.Quotient.mk z) = Submodule.Quotient.mk z.swap := fun z ↦ by
    simp [Submodule.Quotient.equiv_apply]
  -- `rw` would time out checking its result by `rfl`; `simp only` performs the same rewrites.
  simp only [LinearMap.detLineCongr_tmul,
    detLineCongr_detLineShortExactEquiv_ker_tmul f g _ he u w,
    ← TensorProduct.smul_tmul', (detLineProdMapEquiv g f).map_smul,
    detLineProdMapEquiv_tmul g f w u _ _ (coe_detLineShortExactEquiv_ker_tmul g f w u)
      (coe_detLineShortExactEquiv_coker_tmul g f _ _) _ hχ hψ,
    detLineProdMapEquiv_tmul f g u w _ _ (coe_detLineShortExactEquiv_ker_tmul f g u w)
      (coe_detLineShortExactEquiv_coker_tmul f g _ _) φ hψ hχ, LinearMap.comp_apply,
    LinearEquiv.coe_coe, detLineCongr_symm_detLineShortExactEquiv_coker_tmul f g _ hQ,
    map_smul, smul_eq_mul, TensorProduct.comm_tmul, smul_smul]
  congr 1
  generalize φ _ = t
  generalize finrank K (ker f) = a, finrank K (ker g) = b, finrank K (N ⧸ range f) = c,
    finrank K (N' ⧸ range g) = d
  -- The signs agree because `(a + c) * (b + d) + c * b = b * a + d * a + c * d + 2 * (c * b)`.
  have hc : ((-1 : K) ^ (c * b)) ^ 2 = 1 := by rw [pow_right_comm, neg_one_sq, one_pow]
  linear_combination (-(-1 : K) ^ (b * a) * (-1) ^ (d * a) * (-1) ^ (c * d) * t) * hc

/-- **Exchanging the summands of a direct sum.** The exchange of factors
`LinearEquiv.prodComm` carries `f ⊕ g` to `g ⊕ f`, and transporting determinant lines along it
(`LinearMap.detLineCongr`) turns `LinearMap.detLineProdMapEquiv f g` into
`LinearMap.detLineProdMapEquiv g f` followed by the exchange of the tensor factors, up to the sign
`(-1) ^ ((dim (ker f) + dim (coker f)) * (dim (ker g) + dim (coker g)))`. This sign is
`(-1) ^ (ind f * ind g)`, since `dim (ker f) + dim (coker f)` has the parity of the index
`dim (ker f) - dim (coker f)`: it is the Koszul sign rule for the determinant lines, graded by the
index. -/
theorem detLineProdMapEquiv_detLineCongr_prodComm (z : (f.prodMap g).detLine) :
    detLineProdMapEquiv g f ((f.prodMap g).detLineCongr (LinearEquiv.prodComm K M M')
        (LinearEquiv.prodComm K N N') (prodMap_comp_prodComm f g) z) =
      (-1 : K) ^ ((finrank K (ker f) + finrank K (N ⧸ range f)) *
          (finrank K (ker g) + finrank K (N' ⧸ range g))) •
        TensorProduct.comm K _ _ (detLineProdMapEquiv f g z) := by
  -- Functionals taking the value `1` on exterior products of bases of the kernels.
  obtain ⟨ψu, hψu⟩ := exists_dual_detLine_ιMulti_finBasis_eq_one K (ker f)
  obtain ⟨ψw, hψw⟩ := exists_dual_detLine_ιMulti_finBasis_eq_one K (ker g)
  -- The functional `ξ` takes the value `1` at the joined exterior product `β₀` of the bases, so
  -- every element of the line `det (ker (f ⊕ g))` is a multiple of `β₀`.
  have hξ : (dualDistribEquiv K _ _ (ψu ⊗ₜ ψw) ∘ₗ
      (TauCeti.detLineShortExactEquiv (kerInlProdMap_injective f g)
        (exact_kerInlProdMap_kerSndProdMap f g) (kerSndProdMap_surjective f g)).symm.toLinearMap)
      (TauCeti.detLineShortExactEquiv (kerInlProdMap_injective f g)
        (exact_kerInlProdMap_kerSndProdMap f g) (kerSndProdMap_surjective f g)
        (exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) ⊗ₜ
          exteriorPower.ιMulti K _ (Module.finBasis K (ker g)))) = 1 := by
    simp [hψu, hψw]
  -- Both sides are linear in `z`.
  induction z using TensorProduct.inductionOn with
  | add z z' hz hz' => simp only [LinearEquiv.map_add, smul_add, hz, hz']
  | tmul b φ =>
    have : FiniteDimensional K (ker (f.prodMap g)) :=
      TauCeti.finiteDimensional_of_exact (exact_kerInlProdMap_kerSndProdMap f g)
    obtain ⟨c, rfl⟩ : ∃ c : K, c • _ = b :=
      ⟨_, TauCeti.apply_smul_eq_self_of_finrank_eq_one (TauCeti.finrank_detLine K _) hξ b⟩
    simp only [← TensorProduct.smul_tmul', LinearEquiv.map_smul,
      detLineProdMapEquiv_detLineCongr_prodComm_tmul, smul_comm c]

end LinearMap
