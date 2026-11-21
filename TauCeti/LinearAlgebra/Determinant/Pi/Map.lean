/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.Determinant.DirectSum
public import TauCeti.LinearAlgebra.Determinant.Dual
public import TauCeti.LinearAlgebra.Determinant.Pi.Basic
public import TauCeti.LinearAlgebra.Pi.Map
public import TauCeti.LinearAlgebra.Pi.Prod

/-!
# Determinant lines of finite families of maps of even index

The determinant line of a linear map `f : M → N` with finite-dimensional kernel and cokernel is
`det f = det (ker f) ⊗ (det (coker f))^*`. For two maps the direct sum isomorphism
`det (f ⊕ g) ≃ det f ⊗ det g` (`LinearMap.detLineProdMapEquiv`) carries a Koszul sign, and
exchanging `f` and `g` costs `(-1) ^ (ind f * ind g)`
(`LinearMap.detLineProdMapEquiv_detLineCongr_prodComm`). So when every index is even the
determinant line of a finite family of maps should not depend on an ordering of the family. This
file constructs that order-free isomorphism.

Through the pairing `det (V^*) ≃ (det V)^*` (`TauCeti.detLineDualEquiv`) and the product
isomorphism `det U ⊗ det W ≃ det (U × W)` (`TauCeti.detLineProdEquiv`), the determinant line of
`f` is that of the single space `ker f × (coker f)^*`:

`det f ≃ det (ker f × (coker f)^*)` (`LinearMap.detLineEquivProdDual`).

This space has dimension `dim ker f + dim coker f`, which is even exactly when the index
`dim ker f - dim coker f` is. For a finite family `f i : M i → N i` the coordinatewise map
`LinearMap.piMap f` has kernel `∀ i, ker (f i)` and cokernel `∀ i, coker (f i)`
(`LinearMap.kerPiMapEquiv`, `LinearMap.cokerPiMapEquiv`), and the dual of a finite product is the
product of the duals, so

`ker (piMap f) × (coker (piMap f))^* ≃ ∀ i, ker (f i) × (coker (f i))^*`

(`LinearMap.piKerProdDualEquiv`). When every `f i` has even index, every factor on the right is
even-dimensional, and the determinant line of the product is the tensor product of the
determinant lines of its factors over the unordered index set (`TauCeti.detLinePiEquiv`). This
gives the **determinant line of a coordinatewise map of even index**

`det (piMap f) ≃ ⨂ᵢ det (f i)` (`LinearMap.detLinePiMapEquiv`),

with the unordered tensor product `PiTensorProduct`. It is the permutation law of determinant
lines for maps of even index: on pure tensors, after `det (piMap f) ≃ det (ker × coker^*)`, its
inverse is the exterior product of the images of the factors, taken in the order of any
enumeration of the index set (`LinearMap.coe_detLineEquivProdDual_detLinePiMapEquiv_symm_tprod`).
For bijective maps it sends the canonical generator `1` of `det (piMap f)` to the tensor product
of the canonical generators of the `det (f i)`
(`LinearMap.detLinePiMapEquiv_detLineEquivOfBijective_symm_one`), so orientations of invertible
operators multiply.

In Taubes's count of pseudoholomorphic curves with point constraints, each component `C` of a
configuration carries a normal operator together with evaluation at the constraint points on
`C`; these operators have even index, and the configuration is an unordered set of components.
This isomorphism orients the product of their determinant lines without ordering the components.

## Main declarations

* `LinearMap.detLineEquivProdDual`: `det f ≃ det (ker f × (coker f)^*)`, with value
  `LinearMap.coe_detLineEquivProdDual_tmul`.
* `LinearMap.piKerProdDualEquiv`: `∀ i, ker (f i) × (coker (f i))^* ≃
  ker (piMap f) × (coker (piMap f))^*`.
* `LinearMap.detLinePiMapEquiv`: for maps of even index, `det (piMap f) ≃ ⨂ᵢ det (f i)`.
* `LinearMap.coe_detLineEquivProdDual_detLinePiMapEquiv_symm_tprod`: the permutation law, its
  inverse on pure tensors as an exterior product in the order of any enumeration.
* `LinearMap.detLinePiMapEquiv_detLineEquivOfBijective_symm_one`: compatibility with the canonical
  generators of bijective maps.

## References

* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS
  Colloquium Publications **52**, 2012, Appendix A.2 (determinant line bundles).
* C. H. Taubes, *Counting pseudo-holomorphic submanifolds in dimension 4*, J. Differential Geom.
  **44** (1996), 818–893.
-/

public section

noncomputable section

open Module TensorProduct

namespace LinearMap

section Single

variable {K : Type*} [Field K] {M N : Type*} [AddCommGroup M] [Module K M] [AddCommGroup N]
  [Module K N] (f : M →ₗ[K] N) [FiniteDimensional K (ker f)] [FiniteDimensional K (N ⧸ range f)]

/-- **The determinant line of a map as that of a single space.** For `f` with finite-dimensional
kernel and cokernel, `det f = det (ker f) ⊗ (det (coker f))^*` is the determinant line of
`ker f × (coker f)^*`: the dual of the cokernel line is the determinant line of the dual of the
cokernel (`TauCeti.detLineDualEquiv`), and the tensor product of two determinant lines is that of
the product (`TauCeti.detLineProdEquiv`). Its value is `LinearMap.coe_detLineEquivProdDual_tmul`. -/
def detLineEquivProdDual : f.detLine ≃ₗ[K] TauCeti.detLine K (ker f × Dual K (N ⧸ range f)) :=
  TensorProduct.congr (LinearEquiv.refl K _) (TauCeti.detLineDualEquiv K (N ⧸ range f)).symm ≪≫ₗ
    TauCeti.detLineProdEquiv K _ _

/-- `LinearMap.detLineEquivProdDual` sends `(u₁ ∧ ⋯ ∧ uₐ) ⊗ ⟨φ₁ ∧ ⋯ ∧ φ_c⟩`, where the second
factor is the functional `TauCeti.detLineDualEquiv (φ₁ ∧ ⋯ ∧ φ_c)` on the cokernel line, to
`(u₁, 0) ∧ ⋯ ∧ (uₐ, 0) ∧ (0, φ₁) ∧ ⋯ ∧ (0, φ_c)`. -/
@[simp]
theorem coe_detLineEquivProdDual_tmul (u : Fin (finrank K (ker f)) → ker f)
    (φ : Fin (finrank K (Dual K (N ⧸ range f))) → Dual K (N ⧸ range f)) :
    (f.detLineEquivProdDual (exteriorPower.ιMulti K _ u ⊗ₜ
        TauCeti.detLineDualEquiv K _ (exteriorPower.ιMulti K _ φ)) :
        ExteriorAlgebra K (ker f × Dual K (N ⧸ range f))) =
      ExteriorAlgebra.ιMulti K _
        (Fin.append (LinearMap.inl K _ _ ∘ u) (LinearMap.inr K _ _ ∘ φ)) := by
  simp [detLineEquivProdDual]

/-- The space `ker f × (coker f)^*` has dimension `dim ker f + dim coker f`. -/
theorem finrank_ker_prod_dual :
    finrank K (ker f × Dual K (N ⧸ range f)) = finrank K (ker f) + finrank K (N ⧸ range f) := by
  rw [Module.finrank_prod, Subspace.dual_finrank_eq]

/-- For a bijective map, `LinearMap.detLineEquivProdDual` sends the canonical generator of `det f`
(`LinearMap.detLineEquivOfBijective`) to the empty exterior product `1` of the zero space
`ker f × (coker f)^*`. -/
theorem coe_detLineEquivProdDual_detLineEquivOfBijective_symm_one (hf : Function.Bijective f) :
    (f.detLineEquivProdDual ((detLineEquivOfBijective hf).symm 1) :
        ExteriorAlgebra K (ker f × Dual K (N ⧸ range f))) = 1 := by
  have hc := finrank_quotient_range_eq_zero_of_surjective hf.2
  have : IsEmpty (Fin (finrank K (N ⧸ range f))) := by
    rw [hc]
    infer_instance
  -- The functional pairing the empty exterior products of the cokernel and its dual is `1`.
  rw [detLineEquivOfBijective_symm_one hf 0
      (TauCeti.detLineDualEquiv K _ (exteriorPower.ιMulti K _ 0)) 0
      (by rw [TauCeti.detLineDualEquiv_ιMulti_ιMulti, Matrix.det_isEmpty]),
    coe_detLineEquivProdDual_tmul]
  simp [ExteriorAlgebra.ιMulti_apply, finrank_ker_eq_zero_of_injective hf.1, hc]

end Single

section PiCommRing

variable {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] [DecidableEq ι] {M N : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module R (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Module R (N i)]
  (f : ∀ i, M i →ₗ[R] N i)

/-- The space `ker × coker^*` of a coordinatewise map is the product of those of its components:
`ker (piMap f) ≃ ∀ i, ker (f i)` (`LinearMap.kerPiMapEquiv`), and the dual of
`coker (piMap f) ≃ ∀ i, coker (f i)` (`LinearMap.cokerPiMapEquiv`) is the product of the duals
(`LinearMap.lsum`). -/
def piKerProdDualEquiv :
    ((i : ι) → ker (f i) × Dual R (N i ⧸ range (f i))) ≃ₗ[R]
      ker (piMap f) × Dual R (((i : ι) → N i) ⧸ range (piMap f)) :=
  TauCeti.LinearEquiv.arrowProdEquivProdArrow R _ _ ≪≫ₗ
    (kerPiMapEquiv f).symm.prodCongr
      (LinearMap.lsum R (fun i ↦ N i ⧸ range (f i)) R ≪≫ₗ (cokerPiMapEquiv f).dualMap)

@[simp]
theorem coe_piKerProdDualEquiv_apply_fst (x : (i : ι) → ker (f i) × Dual R (N i ⧸ range (f i))) :
    ((piKerProdDualEquiv f x).1 : (i : ι) → M i) = fun i ↦ ((x i).1 : M i) := by
  simp [piKerProdDualEquiv]

/-- The functional component of `LinearMap.piKerProdDualEquiv` evaluates on the class of `y` to
the sum over `i` of the `i`th functional on the class of `y i`. -/
@[simp]
theorem piKerProdDualEquiv_apply_snd_mk (x : (i : ι) → ker (f i) × Dual R (N i ⧸ range (f i)))
    (y : (i : ι) → N i) :
    (piKerProdDualEquiv f x).2 (Submodule.Quotient.mk y) =
      ∑ i, (x i).2 (Submodule.Quotient.mk (y i)) := by
  simp [piKerProdDualEquiv]

end PiCommRing

section Pi

variable {K : Type*} [Field K] {ι : Type*} [Fintype ι] [DecidableEq ι] {M N : ι → Type*}
  [∀ i, AddCommGroup (M i)] [∀ i, Module K (M i)] [∀ i, AddCommGroup (N i)] [∀ i, Module K (N i)]
  (f : ∀ i, M i →ₗ[K] N i)

variable [∀ i, FiniteDimensional K (ker (f i))] [∀ i, FiniteDimensional K (N i ⧸ range (f i))]

omit [Fintype ι] [DecidableEq ι] in
/-- If `dim ker (f i) + dim coker (f i)` is even, so is the dimension of the space
`ker (f i) × (coker (f i))^*` whose determinant line is that of `f i`. -/
theorem even_finrank_ker_prod_dual
    (h : ∀ i, Even (finrank K (ker (f i)) + finrank K (N i ⧸ range (f i)))) (i : ι) :
    Even (finrank K (ker (f i) × Dual K (N i ⧸ range (f i)))) := by
  rw [finrank_ker_prod_dual]
  exact h i

/-- **The determinant line of a coordinatewise map of even index.** Let `f i : M i → N i` be a
finite family of maps with finite-dimensional kernels and cokernels, each of even index, i.e. with
`dim ker (f i) + dim coker (f i)` even. Then the determinant line of `piMap f` is the tensor
product of the determinant lines of the `f i` over the unordered index set:
`det (piMap f) ≃ ⨂ᵢ det (f i)`. It is assembled from `det (f i) ≃ det (ker × coker^*)`
(`LinearMap.detLineEquivProdDual`), the order-free isomorphism of determinant lines of products of
even-dimensional spaces (`TauCeti.detLinePiEquiv`), and the splitting
`LinearMap.piKerProdDualEquiv`. Its inverse on pure tensors is
`LinearMap.coe_detLineEquivProdDual_detLinePiMapEquiv_symm_tprod`. -/
def detLinePiMapEquiv (h : ∀ i, Even (finrank K (ker (f i)) + finrank K (N i ⧸ range (f i)))) :
    (piMap f).detLine ≃ₗ[K] ⨂[K] i, (f i).detLine :=
  ((PiTensorProduct.congr fun i ↦ (f i).detLineEquivProdDual) ≪≫ₗ
    TauCeti.detLinePiEquiv K _ (even_finrank_ker_prod_dual f h) ≪≫ₗ
    (piKerProdDualEquiv f).detLineCongr ≪≫ₗ (piMap f).detLineEquivProdDual.symm).symm

/-- The inverse of `LinearMap.detLinePiMapEquiv` on a pure tensor `⨂ᵢ xᵢ`, after
`det (piMap f) ≃ det (ker × coker^*)`: the image under `LinearMap.piKerProdDualEquiv` of the
`TauCeti.detLinePiEquiv` image of the family of the `det (ker (f i) × coker (f i)^*)` images of the
`xᵢ`. -/
theorem detLineEquivProdDual_detLinePiMapEquiv_symm_tprod
    (h : ∀ i, Even (finrank K (ker (f i)) + finrank K (N i ⧸ range (f i))))
    (x : (i : ι) → (f i).detLine) :
    (piMap f).detLineEquivProdDual ((detLinePiMapEquiv f h).symm (⨂ₜ[K] i, x i)) =
      (piKerProdDualEquiv f).detLineCongr (TauCeti.detLinePiEquiv K _
        (even_finrank_ker_prod_dual f h) (⨂ₜ[K] i, (f i).detLineEquivProdDual (x i))) := by
  simp [detLinePiMapEquiv]

/-- **The permutation law.** For maps of even index, the inverse of `LinearMap.detLinePiMapEquiv`
sends `⨂ᵢ xᵢ` to the element of `det (piMap f) ≃ det (ker × coker^*)` which, in the exterior
algebra of `ker (piMap f) × (coker (piMap f))^*`, is the image under
`LinearMap.piKerProdDualEquiv` of the exterior product of the images of the
`det (ker (f i) × coker (f i)^*)` images of the `xᵢ` under the inclusions of the factors, taken in
the order of any enumeration `e` of the index set. In particular this product does not depend on
`e`. -/
theorem coe_detLineEquivProdDual_detLinePiMapEquiv_symm_tprod
    (h : ∀ i, Even (finrank K (ker (f i)) + finrank K (N i ⧸ range (f i))))
    (x : (i : ι) → (f i).detLine) (e : Fin (Fintype.card ι) ≃ ι) :
    ((piMap f).detLineEquivProdDual ((detLinePiMapEquiv f h).symm (⨂ₜ[K] i, x i)) :
        ExteriorAlgebra K (ker (piMap f) × Dual K (((i : ι) → N i) ⧸ range (piMap f)))) =
      ExteriorAlgebra.map (piKerProdDualEquiv f).toLinearMap
        (List.ofFn fun k ↦ ExteriorAlgebra.map
          (LinearMap.single K (fun i ↦ ker (f i) × Dual K (N i ⧸ range (f i))) (e k))
          ((f (e k)).detLineEquivProdDual (x (e k)) : ExteriorAlgebra K _)).prod := by
  rw [detLineEquivProdDual_detLinePiMapEquiv_symm_tprod, LinearEquiv.coe_detLineCongr,
    TauCeti.coe_detLinePiEquiv_tprod _ _ _ _ e]

/-- **Orientations of invertible maps multiply.** For bijective maps of even index (index zero),
`LinearMap.detLinePiMapEquiv` sends the canonical generator of `det (piMap f)` to the tensor
product of the canonical generators of the `det (f i)` (`LinearMap.detLineEquivOfBijective`). -/
theorem detLinePiMapEquiv_detLineEquivOfBijective_symm_one
    (h : ∀ i, Even (finrank K (ker (f i)) + finrank K (N i ⧸ range (f i))))
    (hf : ∀ i, Function.Bijective (f i)) :
    detLinePiMapEquiv f h ((detLineEquivOfBijective (Function.Bijective.piMap hf)).symm 1) =
      ⨂ₜ[K] i, (detLineEquivOfBijective (hf i)).symm 1 := by
  rw [← LinearEquiv.eq_symm_apply]
  refine (piMap f).detLineEquivProdDual.injective (Subtype.ext ?_)
  rw [coe_detLineEquivProdDual_detLinePiMapEquiv_symm_tprod f h _ (Fintype.equivFin ι).symm,
    coe_detLineEquivProdDual_detLineEquivOfBijective_symm_one (piMap f) (.piMap hf)]
  simp [coe_detLineEquivProdDual_detLineEquivOfBijective_symm_one]

end Pi

end LinearMap
