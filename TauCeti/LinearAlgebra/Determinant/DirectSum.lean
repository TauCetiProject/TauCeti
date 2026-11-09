/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.Line
public import TauCeti.LinearAlgebra.Determinant.Exact
public import TauCeti.LinearAlgebra.Prod
import TauCeti.LinearAlgebra.Exact
import TauCeti.LinearAlgebra.Dual.Contraction
import TauCeti.LinearAlgebra.ExteriorPower.Basic

/-!
# The determinant line of a direct sum

For linear maps `f : M → N` and `g : M' → N'` between vector spaces whose kernels and cokernels
are finite-dimensional, the direct sum `f ⊕ g = f.prodMap g : M × M' → N × N'` has kernel
`ker f × ker g` and cokernel `coker f × coker g`. The short exact sequences

`0 → ker f → ker (f ⊕ g) → ker g → 0` and `0 → coker f → coker (f ⊕ g) → coker g → 0`,

with the inclusions `x ↦ (x, 0)` first and the second projections last, identify the determinant
lines `det (f ⊕ g) = det (ker (f ⊕ g)) ⊗ (det (coker (f ⊕ g)))^*` with
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

* `LinearMap.kerInlProdMap`, `LinearMap.kerInrProdMap`, `LinearMap.cokerInlProdMap`,
  `LinearMap.cokerInrProdMap`: the inclusions of the kernels and cokernels of the summands into
  those of `f.prodMap g`.
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

/-! ### Kernels and cokernels of a direct sum -/

section Ring

variable {R : Type*} [Ring R] {M N M' N' : Type*} [AddCommGroup M] [Module R M]
  [AddCommGroup N] [Module R N] [AddCommGroup M'] [Module R M'] [AddCommGroup N'] [Module R N']
  (f : M →ₗ[R] N) (g : M' →ₗ[R] N')

/-- The inclusion `x ↦ (x, 0)` of `ker f` into `ker (f.prodMap g)`. -/
def kerInlProdMap : ker f →ₗ[R] ker (f.prodMap g) :=
  (inl R M M').restrict fun x hx ↦ by simpa using hx

/-- The inclusion `y ↦ (0, y)` of `ker g` into `ker (f.prodMap g)`. -/
def kerInrProdMap : ker g →ₗ[R] ker (f.prodMap g) :=
  (inr R M M').restrict fun x hx ↦ by simpa using hx

/-- The second projection `ker (f.prodMap g) → ker g`. -/
def kerSndProdMap : ker (f.prodMap g) →ₗ[R] ker g :=
  (snd R M M').restrict fun x hx ↦ by simp_all

@[simp]
theorem coe_kerInlProdMap_apply (x : ker f) :
    (kerInlProdMap f g x : M × M') = ((x : M), 0) :=
  (rfl)

@[simp]
theorem coe_kerInrProdMap_apply (y : ker g) :
    (kerInrProdMap f g y : M × M') = (0, (y : M')) :=
  (rfl)

@[simp]
theorem coe_kerSndProdMap_apply (z : ker (f.prodMap g)) :
    (kerSndProdMap f g z : M') = (z : M × M').2 :=
  (rfl)

@[simp]
theorem kerSndProdMap_comp_kerInrProdMap :
    kerSndProdMap f g ∘ₗ kerInrProdMap f g = LinearMap.id :=
  LinearMap.ext fun _ ↦ Subtype.ext (by simp)

theorem kerInlProdMap_injective : Function.Injective (kerInlProdMap f g) := fun x y h ↦
  Subtype.ext (by simpa using congrArg (fun z : ker (f.prodMap g) ↦ (z : M × M').1) h)

theorem kerSndProdMap_surjective : Function.Surjective (kerSndProdMap f g) := fun y ↦
  ⟨kerInrProdMap f g y, LinearMap.congr_fun (kerSndProdMap_comp_kerInrProdMap f g) y⟩

/-- `0 → ker f → ker (f.prodMap g) → ker g → 0` is exact in the middle. -/
theorem exact_kerInlProdMap_kerSndProdMap :
    Function.Exact (kerInlProdMap f g) (kerSndProdMap f g) := by
  rintro ⟨⟨x, y⟩, hz⟩
  constructor
  · intro h
    have hy : y = 0 := by simpa using congrArg Subtype.val h
    subst hy
    exact ⟨⟨x, by simpa using hz⟩, Subtype.ext (by simp)⟩
  · rintro ⟨x', hx'⟩
    rw [← hx']
    exact Subtype.ext (by simp)

/-- The map `coker f → coker (f.prodMap g)` induced by `x ↦ (x, 0)`. -/
def cokerInlProdMap : N ⧸ range f →ₗ[R] (N × N') ⧸ range (f.prodMap g) :=
  (range f).mapQ _ (inl R N N') fun x ⟨m, hm⟩ ↦ ⟨(m, 0), by simp [hm]⟩

/-- The map `coker g → coker (f.prodMap g)` induced by `y ↦ (0, y)`. -/
def cokerInrProdMap : N' ⧸ range g →ₗ[R] (N × N') ⧸ range (f.prodMap g) :=
  (range g).mapQ _ (inr R N N') fun y ⟨m, hm⟩ ↦ ⟨(0, m), by simp [hm]⟩

/-- The map `coker (f.prodMap g) → coker g` induced by the second projection. -/
def cokerSndProdMap : (N × N') ⧸ range (f.prodMap g) →ₗ[R] N' ⧸ range g :=
  (range (f.prodMap g)).mapQ _ (snd R N N') fun _ ⟨m, hm⟩ ↦ ⟨m.2, by simp [← hm]⟩

@[simp]
theorem cokerInlProdMap_mk (x : N) :
    cokerInlProdMap f g (Submodule.Quotient.mk x) = Submodule.Quotient.mk (x, 0) :=
  (rfl)

@[simp]
theorem cokerInrProdMap_mk (y : N') :
    cokerInrProdMap f g (Submodule.Quotient.mk y) = Submodule.Quotient.mk (0, y) :=
  (rfl)

@[simp]
theorem cokerSndProdMap_mk (z : N × N') :
    cokerSndProdMap f g (Submodule.Quotient.mk z) = Submodule.Quotient.mk z.2 :=
  (rfl)

@[simp]
theorem cokerSndProdMap_comp_cokerInrProdMap :
    cokerSndProdMap f g ∘ₗ cokerInrProdMap f g = LinearMap.id := by
  ext y
  simp

theorem cokerInlProdMap_injective : Function.Injective (cokerInlProdMap f g) := by
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H x =>
    rw [cokerInlProdMap_mk, Submodule.Quotient.mk_eq_zero] at hx
    obtain ⟨⟨m, m'⟩, hm⟩ := hx
    rw [Submodule.Quotient.mk_eq_zero]
    exact ⟨m, by simpa using congrArg Prod.fst hm⟩

theorem cokerSndProdMap_surjective : Function.Surjective (cokerSndProdMap f g) := fun y ↦
  ⟨cokerInrProdMap f g y, LinearMap.congr_fun (cokerSndProdMap_comp_cokerInrProdMap f g) y⟩

/-- `0 → coker f → coker (f.prodMap g) → coker g → 0` is exact in the middle. -/
theorem exact_cokerInlProdMap_cokerSndProdMap :
    Function.Exact (cokerInlProdMap f g) (cokerSndProdMap f g) := by
  intro z
  induction z using Submodule.Quotient.induction_on with
  | H z =>
    obtain ⟨x, y⟩ := z
    rw [cokerSndProdMap_mk, Submodule.Quotient.mk_eq_zero]
    constructor
    · rintro ⟨m', hm'⟩
      refine ⟨Submodule.Quotient.mk x, ?_⟩
      rw [cokerInlProdMap_mk, Submodule.Quotient.eq]
      exact ⟨(0, -m'), by simp [hm']⟩
    · rintro ⟨x', hx'⟩
      induction x' using Submodule.Quotient.induction_on with
      | H x' =>
        rw [cokerInlProdMap_mk, Submodule.Quotient.eq] at hx'
        obtain ⟨⟨m, m'⟩, hm⟩ := hx'
        have hm' : g m' = -y := by simpa using congrArg Prod.snd hm
        exact ⟨-m', by simp [hm']⟩

end Ring

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
      ExteriorAlgebra.ιMulti K _ (Fin.append (kerInlProdMap f g ∘ u) (kerInrProdMap f g ∘ w)) := by
  have hw : w = kerSndProdMap f g ∘ kerInrProdMap f g ∘ w := by
    rw [← Function.comp_assoc, ← LinearMap.coe_comp, kerSndProdMap_comp_kerInrProdMap,
      LinearMap.id_coe, Function.id_comp]
  conv_lhs => rw [hw]
  rw [TauCeti.coe_detLineShortExactEquiv_tmul]

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
        (Fin.append (cokerInlProdMap f g ∘ x) (cokerInrProdMap f g ∘ y)) := by
  have hy : y = cokerSndProdMap f g ∘ cokerInrProdMap f g ∘ y := by
    rw [← Function.comp_assoc, ← LinearMap.coe_comp, cokerSndProdMap_comp_cokerInrProdMap,
      LinearMap.id_coe, Function.id_comp]
  conv_lhs => rw [hy]
  rw [TauCeti.coe_detLineShortExactEquiv_tmul]

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
  -- Mathlib's `LinearEquiv.smulOfUnit` has no application lemma; it is scalar multiplication.
  rw [show ∀ z, LinearEquiv.smulOfUnit (M := f.detLine ⊗[K] g.detLine)
      ((-1) ^ (finrank K (N ⧸ range f) * finrank K (ker g))) z =
        (-1 : K) ^ (finrank K (N ⧸ range f) * finrank K (ker g)) • z from fun _ ↦ by
      simp [LinearEquiv.smulOfUnit, Units.smul_def], smul_comm, smul_smul]

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
    ExteriorAlgebra.map_apply_ιMulti, TauCeti.ExteriorAlgebra.ιMulti_comp_append, hu, hw,
    Submodule.coe_smul, coe_detLineShortExactEquiv_ker_tmul, ← ExteriorAlgebra.ιMulti_mul_ιMulti,
    TauCeti.ExteriorAlgebra.ιMulti_mul_ιMulti_eq_neg_one_pow_smul]

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
    coe_detLineShortExactEquiv_coker_tmul, ExteriorAlgebra.map_apply_ιMulti,
    TauCeti.ExteriorAlgebra.ιMulti_comp_append, hy, hx, Submodule.coe_smul,
    coe_detLineShortExactEquiv_coker_tmul, ← ExteriorAlgebra.ιMulti_mul_ιMulti,
    TauCeti.ExteriorAlgebra.ιMulti_mul_ιMulti_eq_neg_one_pow_smul]

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
  obtain ⟨ψ, hψ⟩ := Module.Projective.exists_dual_eq_one K
    (show (exteriorPower.ιMulti K _ (Module.finBasis K (N ⧸ range f)) :
        TauCeti.detLine K (N ⧸ range f)) ≠ 0 from
      (exteriorPower.ιMulti_ne_zero_iff _).2 (Module.finBasis K _).linearIndependent)
  obtain ⟨χ, hχ⟩ := Module.Projective.exists_dual_eq_one K
    (show (exteriorPower.ιMulti K _ (Module.finBasis K (N' ⧸ range g)) :
        TauCeti.detLine K (N' ⧸ range g)) ≠ 0 from
      (exteriorPower.ιMulti_ne_zero_iff _).2 (Module.finBasis K _).linearIndependent)
  have he : ∀ z : ker (f.prodMap g), ((LinearEquiv.prodComm K M M').ofSubmodules _ _
      (f.prodMap g |>.map_ker_eq_ker_of_comp_eq (LinearEquiv.prodComm K M M').surjective
        (LinearEquiv.prodComm K N N').injective (prodMap_comp_prodComm f g)) z : M' × M) =
      (z : M × M').swap := fun _ ↦ rfl
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
  -- The signs agree because `2 * (dim (coker f) * dim (ker g))` is even.
  have h : (finrank K (ker f) + finrank K (N ⧸ range f)) *
      (finrank K (ker g) + finrank K (N' ⧸ range g)) +
      finrank K (N ⧸ range f) * finrank K (ker g) =
      finrank K (ker g) * finrank K (ker f) + finrank K (N' ⧸ range g) * finrank K (ker f) +
        finrank K (N ⧸ range f) * finrank K (N' ⧸ range g) +
        2 * (finrank K (N ⧸ range f) * finrank K (ker g)) := by
    ring
  generalize φ _ = t
  conv_rhs => rw [← mul_assoc, ← pow_add, h, pow_add _ _ (2 * _), pow_mul, neg_one_sq, one_pow,
    mul_one]
  ring

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
  obtain ⟨ψu, hψu⟩ := Module.Projective.exists_dual_eq_one K
    (show (exteriorPower.ιMulti K _ (Module.finBasis K (ker f)) :
        TauCeti.detLine K (ker f)) ≠ 0 from
      (exteriorPower.ιMulti_ne_zero_iff _).2 (Module.finBasis K _).linearIndependent)
  obtain ⟨ψw, hψw⟩ := Module.Projective.exists_dual_eq_one K
    (show (exteriorPower.ιMulti K _ (Module.finBasis K (ker g)) :
        TauCeti.detLine K (ker g)) ≠ 0 from
      (exteriorPower.ιMulti_ne_zero_iff _).2 (Module.finBasis K _).linearIndependent)
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
