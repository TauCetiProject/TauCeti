/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.AlgebraicGroup.Hopf.CentralPoint
public import TauCeti.Algebra.AlgebraicGroup.Hopf.Conjugation.Basic
public import TauCeti.Algebra.AlgebraicGroup.Hopf.PointConjugation

/-!
# Regular class functions

For a commutative Hopf algebra `H` over a commutative semiring `k`, with affine group scheme
`G = Spec H`, a regular class function is a function `f ∈ H` with `f(g x g⁻¹) = f(x)` for all
points `g, x` of `G` with values in every commutative `k`-algebra, nonreduced ones included.
They form the subalgebra `classFunctions k H`, defined as the equalizer of the coordinate map
of left conjugation `c* : H → H ⊗[k] H` and the second-factor inclusion `f ↦ 1 ⊗ f`. It is the
coordinate algebra of the conjugacy quotient `Spec H → Spec (classFunctions k H)`, the algebra
`O(G)^G` of invariants of the conjugation action of `G` on itself.

The equalizer presentation and the pointwise description agree
(`TauCeti.HopfAlgebra.mem_classFunctions_iff_forall`): the forward direction evaluates the
equation `c*(f) = 1 ⊗ f` at a pair of points, and the converse takes the two universal
tensor-factor points of `H ⊗[k] H`, whose conjugate is `c*` itself.

A bialgebra map `H' → H`, that is a morphism of group schemes `Spec H → Spec H'`, sends class
functions to class functions (`TauCeti.HopfAlgebra.classFunctionsMap`), functorially. Every
function is a class function exactly when the group is commutative, that is when `H` is
cocommutative (`TauCeti.HopfAlgebra.classFunctions_eq_top_iff_isCocomm`); for instance every
Laurent polynomial is a class function on the multiplicative group.

## Main declarations

* `TauCeti.HopfAlgebra.classFunctions`: the subalgebra of regular class functions.
* `TauCeti.HopfAlgebra.mem_classFunctions_iff`: the equalizer equation `c*(f) = 1 ⊗ f`.
* `TauCeti.HopfAlgebra.mem_classFunctions_iff_forall`: invariance under conjugation of points
  with values in every commutative algebra.
* `TauCeti.HopfAlgebra.pointConjugationAlgHom_apply_of_mem_classFunctions`: conjugation by a
  rational point fixes class functions.
* `TauCeti.HopfAlgebra.classFunctionsMap`: the algebra map of class functions induced by a
  bialgebra map, with `classFunctionsMap_id` and `classFunctionsMap_comp`.
* `TauCeti.HopfAlgebra.classFunctions_eq_top_iff_isCocomm`: all functions are class functions
  exactly for commutative group schemes.

## References

* R. Steinberg, *Regular elements of semisimple algebraic groups*, Publ. Math. IHÉS 25 (1965),
  §6.
* M. Kisin and R. Zhou, *Independence of ℓ for Frobenius conjugacy classes attached to abelian
  varieties*, arXiv:2103.09945, §5.1.3.
-/

public section

open TensorProduct WithConv

namespace TauCeti

namespace HopfAlgebra

universe u v w

section Semiring

variable (k : Type u) (H : Type v) [CommSemiring k] [CommSemiring H] [_root_.HopfAlgebra k H]

/-- The algebra of **regular class functions** of a commutative Hopf algebra `H` over `k`: the
equalizer of the coordinate map of left conjugation `H → H ⊗[k] H` (conjugating point in the first
factor) and the second-factor inclusion `f ↦ 1 ⊗ f`. An element lies in it exactly when its values
at `g * x * g⁻¹` and at `x` agree for all points with values in every commutative `k`-algebra
(`TauCeti.HopfAlgebra.mem_classFunctions_iff_forall`). It is the coordinate algebra of the
conjugacy quotient of `Spec H`. -/
noncomputable def classFunctions : Subalgebra k H :=
  AlgHom.equalizer (conjugationAlgHom (R := k) (H := H))
    (Algebra.TensorProduct.includeRight (R := k) (A := H) (B := H))

/-- The class functions are the equalizer of the coordinate map of conjugation and the
second-factor inclusion. -/
theorem classFunctions_eq_equalizer :
    classFunctions k H =
      AlgHom.equalizer (conjugationAlgHom (R := k) (H := H))
        (Algebra.TensorProduct.includeRight (R := k) (A := H) (B := H)) :=
  (rfl)

variable {k H}

/-- An element is a class function exactly when the coordinate map of conjugation sends it to
`1 ⊗ f`. -/
@[simp]
theorem mem_classFunctions_iff {f : H} :
    f ∈ classFunctions k H ↔ conjugationAlgHom (R := k) (H := H) f = 1 ⊗ₜ[k] f :=
  AlgHom.mem_equalizer _ _ f

/-- A class function takes the same value at `g * x * g⁻¹` and at `x`, for points `g` and `x`
with values in any commutative `k`-algebra. -/
theorem apply_mul_mul_inv_of_mem_classFunctions {f : H} (hf : f ∈ classFunctions k H)
    {A : Type w} [CommSemiring A] [Algebra k A] (g x : WithConv (H →ₐ[k] A)) :
    (g * x * g⁻¹).ofConv f = x.ofConv f := by
  rw [← productMap_comp_conjugationAlgHom g x, AlgHom.comp_apply, mem_classFunctions_iff.mp hf,
    Algebra.TensorProduct.productMap_apply_tmul, map_one, one_mul]

/-- **Conjugation by a rational point fixes every class function.** -/
theorem pointConjugationAlgHom_apply_of_mem_classFunctions {f : H}
    (hf : f ∈ classFunctions k H) (g : WithConv (H →ₐ[k] k)) :
    pointConjugationAlgHom g f = f := by
  simpa [mem_classFunctions_iff.mp hf] using LinearMap.apply_pointConjugationAlgHom LinearMap.id g f

/-- **Class functions are the conjugation-invariant functions.** An element `f` is a class
function exactly when `f(g * x * g⁻¹) = f(x)` for all points `g` and `x` with values in every
commutative `k`-algebra. Algebras in the universe of `H` suffice: the converse uses only the two
universal tensor-factor points of `H ⊗[k] H`. -/
theorem mem_classFunctions_iff_forall {f : H} :
    f ∈ classFunctions k H ↔ ∀ (A : Type v) [CommSemiring A] [Algebra k A]
      (g x : WithConv (H →ₐ[k] A)), (g * x * g⁻¹).ofConv f = x.ofConv f := by
  refine ⟨fun hf A _ _ g x ↦ apply_mul_mul_inv_of_mem_classFunctions hf g x, fun h ↦ ?_⟩
  have hc := comp_conjugationAlgHom (R := k) (H := H) (AlgHom.id k (H ⊗[k] H))
  simp only [AlgHom.id_comp] at hc
  rw [mem_classFunctions_iff, hc, h, ofConv_toConv, Algebra.TensorProduct.includeRight_apply]

/-- The class functions are the whole coordinate algebra exactly when the coordinate map of
conjugation is the second-factor inclusion. -/
theorem classFunctions_eq_top_iff :
    classFunctions k H = ⊤ ↔
      conjugationAlgHom (R := k) (H := H) = Algebra.TensorProduct.includeRight := by
  refine ⟨fun h ↦ AlgHom.ext fun f ↦ mem_classFunctions_iff.mp (h ▸ Algebra.mem_top),
    fun h ↦ eq_top_iff.mpr fun f _ ↦ mem_classFunctions_iff.mpr (by simp [h])⟩

/-- **Every function is a class function exactly on a commutative group scheme.** The class
functions of `H` are all of `H` if and only if `H` is cocommutative: the conjugation action is
trivial exactly when the two universal tensor-factor points commute. -/
theorem classFunctions_eq_top_iff_isCocomm :
    classFunctions k H = ⊤ ↔ _root_.Coalgebra.IsCocomm k H := by
  rw [classFunctions_eq_top_iff, ← commute_includeLeft_includeRight_iff_isCocomm,
    ← (WithConv.toConv_injective (A := H →ₐ[k] H ⊗[k] H)).eq_iff, toConv_conjugationAlgHom,
    Bialgebra.TensorProduct.includeLeft_toAlgHom, Bialgebra.TensorProduct.includeRight_toAlgHom,
    mul_inv_eq_iff_eq_mul, commute_iff_eq]

/-- On a commutative group scheme every function is a class function. -/
@[simp]
theorem classFunctions_eq_top [_root_.Coalgebra.IsCocomm k H] : classFunctions k H = ⊤ :=
  classFunctions_eq_top_iff_isCocomm.mpr inferInstance

end Semiring

section Map

variable {k : Type u} [CommSemiring k]
variable {H₁ : Type v} {H₂ : Type w} {H₃ : Type*} [CommSemiring H₁] [CommSemiring H₂]
  [CommSemiring H₃] [_root_.HopfAlgebra k H₁] [_root_.HopfAlgebra k H₂] [_root_.HopfAlgebra k H₃]

/-- A bialgebra map, that is a morphism of group schemes in the opposite direction, sends class
functions to class functions. -/
theorem map_mem_classFunctions (φ : H₁ →ₐc[k] H₂) {f : H₁} (hf : f ∈ classFunctions k H₁) :
    φ f ∈ classFunctions k H₂ := by
  rw [mem_classFunctions_iff] at hf ⊢
  have h := congrArg (fun ψ : H₁ →ₐ[k] H₂ ⊗[k] H₂ ↦ ψ f)
    (tensorProduct_map_comp_conjugationAlgHom (R := k) (H := H₁) φ)
  simp only [AlgHom.comp_apply, hf, Algebra.TensorProduct.map_tmul, map_one] at h
  exact h.symm

/-- The image of the class functions under a bialgebra map consists of class functions. -/
theorem map_classFunctions_le (φ : H₁ →ₐc[k] H₂) :
    (classFunctions k H₁).map (φ : H₁ →ₐ[k] H₂) ≤ classFunctions k H₂ := by
  rintro _ ⟨f, hf, rfl⟩
  exact map_mem_classFunctions φ hf

/-- The algebra map of class functions induced by a bialgebra map `H₁ → H₂`, the restriction of
that map. Geometrically it is the map of conjugacy quotients induced by a morphism of group
schemes `Spec H₂ → Spec H₁`. -/
noncomputable def classFunctionsMap (φ : H₁ →ₐc[k] H₂) :
    classFunctions k H₁ →ₐ[k] classFunctions k H₂ :=
  ((φ : H₁ →ₐ[k] H₂).comp (classFunctions k H₁).val).codRestrict _
    fun f ↦ map_mem_classFunctions φ f.property

@[simp]
theorem coe_classFunctionsMap (φ : H₁ →ₐc[k] H₂) (f : classFunctions k H₁) :
    (classFunctionsMap φ f : H₂) = φ f :=
  (rfl)

/-- The induced map of class functions is the restriction of the bialgebra map. -/
theorem val_comp_classFunctionsMap (φ : H₁ →ₐc[k] H₂) :
    (classFunctions k H₂).val.comp (classFunctionsMap φ) =
      (φ : H₁ →ₐ[k] H₂).comp (classFunctions k H₁).val :=
  AlgHom.ext fun _ ↦ coe_classFunctionsMap φ _

@[simp]
theorem classFunctionsMap_id :
    classFunctionsMap (BialgHom.id k H₁) = AlgHom.id k (classFunctions k H₁) :=
  AlgHom.ext fun _ ↦ Subtype.ext (coe_classFunctionsMap _ _)

theorem classFunctionsMap_comp (ψ : H₂ →ₐc[k] H₃) (φ : H₁ →ₐc[k] H₂) :
    classFunctionsMap (ψ.comp φ) = (classFunctionsMap ψ).comp (classFunctionsMap φ) :=
  AlgHom.ext fun _ ↦ Subtype.ext (coe_classFunctionsMap _ _)

end Map

end HopfAlgebra

end TauCeti
