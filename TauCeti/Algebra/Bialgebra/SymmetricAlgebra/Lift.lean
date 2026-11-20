/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Bialgebra.Hom
public import TauCeti.Algebra.Bialgebra.ReducedComul
public import TauCeti.Algebra.WordFiltration.Basic
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Primitive
import Mathlib.Algebra.Algebra.Rat
import Mathlib.LinearAlgebra.Basis.VectorSpace
import Mathlib.RingTheory.Flat.Basic
import Mathlib.Tactic.LinearCombination
import TauCeti.LinearAlgebra.TensorProduct.Submodule

/-!
# Bialgebra maps out of a symmetric algebra

A linear map `f : M → A` into a commutative bialgebra whose values are primitive extends to the
algebra map `SymmetricAlgebra R M → A`, and this extension is a bialgebra map, because the
generators `ι m` of the symmetric algebra are primitive. So bialgebra maps out of
`SymmetricAlgebra R M` correspond to linear maps from `M` to the primitive elements.

Over a field of characteristic zero the extension of an injective map is injective: linearly
independent primitive elements of a commutative bialgebra are algebraically independent. The
proof is by induction along the degree filtration of the symmetric algebra. An element `x` of
degree at most `d + 1` has reduced coproduct `Δ x - x ⊗ 1 - 1 ⊗ x + ε(x) (1 ⊗ 1)` of bidegree at
most `(d, d)`. If `x` is in the kernel, the bialgebra map is injective in degree `d` by induction,
so this reduced coproduct vanishes, `x - ε(x)` is primitive, and in characteristic zero it is
therefore a generator `ι m`; injectivity of `f` forces it to vanish. In positive characteristic
the statement is false: `x ^ p` is primitive in `SymmetricAlgebra k k`.

## Main declarations

* `SymmetricAlgebra.liftBialgHom`: the bialgebra map extending a linear map with primitive
  values.
* `SymmetricAlgebra.liftBialgHom_injective`: over a field of characteristic zero it is injective
  when the linear map is.

## References

* J. W. Milnor and J. C. Moore, *On the structure of Hopf algebras*, Ann. of Math. 81 (1965),
  211–264.
-/

public section

open TensorProduct TauCeti.Algebra TauCeti.Bialgebra

namespace SymmetricAlgebra

section Lift

variable {R M A : Type*} [CommSemiring R] [AddCommMonoid M] [Module R M] [CommSemiring A]
  [Bialgebra R A]

omit [CommSemiring A] [Bialgebra R A] in
/-- The generators of a symmetric algebra are primitive. -/
theorem isPrimitiveElem_ι (m : M) : Bialgebra.IsPrimitiveElem R (ι R M m) :=
  ⟨counit_ι R M m, by simp [add_comm]⟩

/-- The bialgebra map out of a symmetric algebra extending a linear map whose values are
primitive. -/
noncomputable def liftBialgHom (f : M →ₗ[R] A) (hf : ∀ m, Bialgebra.IsPrimitiveElem R (f m)) :
    SymmetricAlgebra R M →ₐc[R] A :=
  BialgHom.ofAlgHom (lift f)
    (algHom_ext <| LinearMap.ext fun m ↦ by simp [(hf m).counit_eq_zero, algebraMapInv_ι])
    (algHom_ext <| LinearMap.ext fun m ↦ by
      simp [(hf m).comul_eq_tmul_add_tmul, add_comm])

/-- As an algebra map, `liftBialgHom f hf` is the extension `lift f`. -/
@[simp]
theorem liftBialgHom_apply (f : M →ₗ[R] A) (hf : ∀ m, Bialgebra.IsPrimitiveElem R (f m))
    (x : SymmetricAlgebra R M) : liftBialgHom f hf x = lift f x :=
  (rfl)

/-- `liftBialgHom f hf` extends `f`. -/
theorem liftBialgHom_ι (f : M →ₗ[R] A) (hf : ∀ m, Bialgebra.IsPrimitiveElem R (f m)) (m : M) :
    liftBialgHom f hf (ι R M m) = f m := by
  simp

/-- A bialgebra map out of a symmetric algebra is the extension of its restriction to the
generators. -/
theorem eq_liftBialgHom (φ : SymmetricAlgebra R M →ₐc[R] A) :
    φ = liftBialgHom ((φ : SymmetricAlgebra R M →ₗ[R] A) ∘ₗ ι R M)
      (fun m ↦ by simpa using (isPrimitiveElem_ι m).map φ) := by
  apply BialgHom.coe_toAlgHom_injective
  apply algHom_ext
  ext m
  simp

end Lift

section Filtration

variable {k M : Type*} [CommRing k] [AddCommMonoid M] [Module k M]

local notation "S" => SymmetricAlgebra k M
local notation "F" => wordFiltration (ι k M)

variable (k M) in
/-- The span of the tensors `p ⊗ q` with `p` and `q` of degree at most `d`. -/
private abbrev tensorFiltration (d : ℕ) : Submodule k (S ⊗[k] S) :=
  LinearMap.range (TensorProduct.map (F d).subtype (F d).subtype)

private theorem tmul_mem_tensorFiltration {d : ℕ} {p q : S} (hp : p ∈ F d) (hq : q ∈ F d) :
    p ⊗ₜ[k] q ∈ tensorFiltration k M d :=
  ⟨⟨p, hp⟩ ⊗ₜ ⟨q, hq⟩, rfl⟩

/-- Multiplying by a tensor `a ⊗ b` with `a` and `b` of degree at most one raises the tensor
filtration by one. -/
private theorem mul_mem_tensorFiltration_succ {d : ℕ} {t : S ⊗[k] S}
    (ht : t ∈ tensorFiltration k M d) {a b : S} (ha : a ∈ F 1) (hb : b ∈ F 1) :
    t * (a ⊗ₜ[k] b) ∈ tensorFiltration k M (d + 1) := by
  have h := Submodule.map₂_tmul_mul_le (F d) (F 1) (F d) (F 1)
  rw [wordFiltration_mul] at h
  rw [tensorFiltration, ← TensorProduct.mapIncl, TensorProduct.range_mapIncl] at ht ⊢
  exact h (Submodule.mul_mem_mul ht (Submodule.apply_mem_map₂ _ ha hb))

/-- The reduced coproduct of a product with a generator. -/
private theorem reducedComul_mul_ι (a : S) (m : M) :
    reducedComul k S (a * ι k M m) =
      reducedComul k S a * (ι k M m ⊗ₜ[k] 1 + 1 ⊗ₜ[k] ι k M m) + a ⊗ₜ[k] ι k M m +
        ι k M m ⊗ₜ[k] a - algebraMap k (S ⊗[k] S) (Coalgebra.counit (R := k) a) *
          (ι k M m ⊗ₜ[k] 1 + 1 ⊗ₜ[k] ι k M m) := by
  -- Express every pure tensor through the four factors `a ⊗ 1`, `1 ⊗ a`, `ι m ⊗ 1`,
  -- `1 ⊗ ι m`, after which the identity is one of commutative rings.
  have h₁ : (a * ι k M m) ⊗ₜ[k] (1 : S) = (a ⊗ₜ[k] 1) * (ι k M m ⊗ₜ[k] 1) := by simp
  have h₂ : (1 : S) ⊗ₜ[k] (a * ι k M m) = (1 ⊗ₜ[k] a) * (1 ⊗ₜ[k] ι k M m) := by simp
  have h₃ : a ⊗ₜ[k] ι k M m = (a ⊗ₜ[k] 1) * (1 ⊗ₜ[k] ι k M m) := by simp
  have h₄ : ι k M m ⊗ₜ[k] a = (ι k M m ⊗ₜ[k] 1) * (1 ⊗ₜ[k] a) := by simp
  simp only [reducedComul_apply, Bialgebra.comul_mul, comul_ι, Bialgebra.counit_mul, counit_ι,
    mul_zero, map_zero, add_zero, h₁, h₂, h₃, h₄]
  ring

/-- An element of degree at most one, a scalar plus a generator, has zero reduced coproduct
defect. -/
private theorem reducedComul_eq_zero_of_mem_one {x : S} (hx : x ∈ F 1) :
    reducedComul k S x = 0 := by
  rw [wordFiltration_eq_pow, pow_one] at hx
  obtain ⟨y, hy, z, ⟨m, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hx
  obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hy
  simp [(isPrimitiveElem_ι m).reducedComul_eq_zero]

/-- **The reduced coproduct of an element of degree at most `d + 1` has bidegree at most
`(d, d)`.** -/
private theorem reducedComul_mem_tensorFiltration (d : ℕ) {x : S} (hx : x ∈ F (d + 1)) :
    reducedComul k S x ∈ tensorFiltration k M d := by
  induction d generalizing x with
  | zero => simp [reducedComul_eq_zero_of_mem_one hx]
  | succ d ih =>
    rw [← wordFiltration_mul (ι k M) (d + 1) 1] at hx
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem a ha b hb =>
      rw [wordFiltration_eq_pow, pow_one] at hb
      obtain ⟨y, hy, z, ⟨m, rfl⟩, rfl⟩ := Submodule.mem_sup.mp hb
      obtain ⟨c, rfl⟩ := Submodule.mem_one.mp hy
      have hι : ι k M m ∈ F 1 := apply_mem_wordFiltration_one _ m
      have h1 : (1 : S) ∈ F 1 := one_mem_wordFiltration _ 1
      have hι' : ι k M m ∈ F (d + 1) := wordFiltration_mono _ (by omega) hι
      have hred := ih ha
      rw [mul_add, map_add, mul_comm, ← Algebra.smul_def, map_smul, reducedComul_mul_ι]
      have hmono := TensorProduct.range_mapIncl_mono (wordFiltration_mono (ι k M) d.le_succ)
        (wordFiltration_mono (ι k M) d.le_succ)
      refine add_mem (Submodule.smul_mem _ _ (hmono hred)) ?_
      refine sub_mem (add_mem (add_mem ?_ ?_) ?_) ?_
      · rw [mul_add]
        exact add_mem (mul_mem_tensorFiltration_succ hred hι h1)
          (mul_mem_tensorFiltration_succ hred h1 hι)
      · exact tmul_mem_tensorFiltration ha hι'
      · exact tmul_mem_tensorFiltration hι' ha
      · rw [← Algebra.smul_def]
        exact Submodule.smul_mem _ _ (add_mem
          (tmul_mem_tensorFiltration hι' (one_mem_wordFiltration _ _))
          (tmul_mem_tensorFiltration (one_mem_wordFiltration _ _) hι'))
    | add x hx y hy ihx ihy => simpa using add_mem ihx ihy

end Filtration

section InjOn

variable {k M A : Type*} [Field k] [AddCommMonoid M] [Module k M] [CommRing A] [Bialgebra k A]

local notation "S" => SymmetricAlgebra k M
local notation "F" => wordFiltration (ι k M)

/-- If a bialgebra map out of the symmetric algebra is injective in degree at most `d`, then
every kernel element of degree at most `d + 1` has vanishing reduced coproduct defect. -/
private theorem reducedComul_eq_zero_of_injOn {φ : S →ₐc[k] A} {d : ℕ}
    (hd : Set.InjOn φ (F d)) {x : S} (hx : x ∈ F (d + 1)) (hφx : φ x = 0) :
    reducedComul k S x = 0 := by
  obtain ⟨u, hu⟩ := reducedComul_mem_tensorFiltration d hx
  -- Over a field every module is flat, so tensoring the two injective restrictions of `φ`
  -- gives an injective map.
  have hinj : Function.Injective ((φ : S →ₗ[k] A) ∘ₗ (F d).subtype) := fun p q hpq ↦
    Subtype.ext (hd p.property q.property hpq)
  have hu0 : u = 0 := by
    apply TensorProduct.map_injective_of_flat_flat _ _ hinj hinj
    rw [map_zero, TensorProduct.map_comp, LinearMap.comp_apply, hu, φ.map_reducedComul, hφx,
      map_zero]
  rw [← hu, hu0, map_zero]

/-- The induction step: if the extension of an injective linear map with primitive values is
injective in degree at most `d`, it is injective in degree at most `d + 1`. A kernel element `x`
has vanishing reduced coproduct defect, so `x - ε(x)` is primitive, hence a generator `ι m` in
characteristic zero, and then `f m = -ε(x)` forces `m = 0` and `x = 0`. -/
private theorem injOn_wordFiltration_succ [CharZero k] {f : M →ₗ[k] A}
    (hf : ∀ m, Bialgebra.IsPrimitiveElem k (f m)) (hinj : Function.Injective f) {d : ℕ}
    (hd : Set.InjOn (liftBialgHom f hf) (F d)) : Set.InjOn (liftBialgHom f hf) (F (d + 1)) := by
  -- It suffices that a kernel element `x` of degree at most `d + 1` vanishes.
  suffices h : ∀ x ∈ F (d + 1), liftBialgHom f hf x = 0 → x = 0 by
    intro x hx y hy hxy
    exact sub_eq_zero.mp (h _ (sub_mem hx hy) (by rw [map_sub, hxy, sub_self]))
  intro x hx hφx
  have hred := reducedComul_eq_zero_of_injOn hd hx hφx
  set c := Coalgebra.counit (R := k) x
  have hprim : Bialgebra.IsPrimitiveElem k (x - algebraMap k S c) := by
    refine Bialgebra.isPrimitiveElem_iff_comul_eq_tmul_add_tmul.mpr ?_
    rw [reducedComul_apply] at hred
    rw [map_sub, Bialgebra.comul_algebraMap, tmul_sub, sub_tmul,
      ← Algebra.TensorProduct.algebraMap_apply, ← Algebra.TensorProduct.algebraMap_apply']
    linear_combination hred
  obtain ⟨m, hm⟩ := (isPrimitiveElem_iff_mem_range_ι _).mp hprim
  have hfm : f m = -algebraMap k A c := by
    rw [← liftBialgHom_ι f hf, hm, map_sub, hφx, zero_sub, AlgHomClass.commutes]
  have hc : c = 0 := by
    simpa [hfm] using (hf m).counit_eq_zero
  have hm0 : m = 0 := hinj (by rw [hfm, hc, map_zero, neg_zero, map_zero])
  simpa [hc, hm0, sub_eq_zero] using hm.symm

/-- By induction on the degree, the extension of an injective linear map with primitive values is
injective on each step of the degree filtration. -/
private theorem injOn_wordFiltration [CharZero k] {f : M →ₗ[k] A}
    (hf : ∀ m, Bialgebra.IsPrimitiveElem k (f m)) (hinj : Function.Injective f) (d : ℕ) :
    Set.InjOn (liftBialgHom f hf) (F d) := by
  induction d with
  | zero =>
    intro x hx y hy hxy
    rw [SetLike.mem_coe, wordFiltration_zero, Submodule.mem_one] at hx hy
    obtain ⟨c, rfl⟩ := hx
    obtain ⟨e, rfl⟩ := hy
    have := congrArg (Coalgebra.counit (R := k)) hxy
    simp only [AlgHomClass.commutes, Bialgebra.counit_algebraMap] at this
    rw [this]
  | succ d ih => exact injOn_wordFiltration_succ hf hinj ih

end InjOn

section Injective

variable {k M A : Type*} [Field k] [AddCommMonoid M] [Module k M] [CommSemiring A]
  [Bialgebra k A]

local notation "F" => wordFiltration (ι k M)

/-- **Over a field of characteristic zero, the bialgebra map out of a symmetric algebra
extending an injective linear map with primitive values is injective.** Equivalently, linearly
independent primitive elements of a commutative bialgebra are algebraically independent. -/
theorem liftBialgHom_injective [CharZero k] {f : M →ₗ[k] A}
    (hf : ∀ m, Bialgebra.IsPrimitiveElem k (f m)) (hinj : Function.Injective f) :
    Function.Injective (liftBialgHom f hf) := by
  -- An algebra over a field is a ring, so the degreewise injectivity applies.
  let : CommRing A := { Algebra.semiringToRing k with mul_comm := mul_comm }
  -- Every element lies in some step of the degree filtration.
  have hmem := exists_mem_wordFiltration_of_iSup_eq_top (ι k M)
    (by rw [iSup_wordFiltration_eq_adjoin, adjoin_range_ι, Algebra.top_toSubmodule])
  intro x y hxy
  obtain ⟨d, hd⟩ := hmem x
  obtain ⟨e, he⟩ := hmem y
  exact injOn_wordFiltration hf hinj (max d e) (wordFiltration_mono _ (le_max_left d e) hd)
    (wordFiltration_mono _ (le_max_right d e) he) hxy

end Injective

end SymmetricAlgebra
