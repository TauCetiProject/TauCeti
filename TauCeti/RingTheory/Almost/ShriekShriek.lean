/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Algebra.Unitization
public import TauCeti.RingTheory.Almost.Algebra

/-!
# The unitisation `B_!!` of an almost algebra

Let `S = (V, m)` be a basic setup and `m~ = m ⊗[V] m`. For a commutative `V`-algebra `R`, the
`V`-module `R_! = m~ ⊗[V] R` is a commutative non-unital `V`-algebra, with product
`(s ⊗ a) * (t ⊗ b) = (s * t) ⊗ (a * b)`, where `s * t` is the action of the image of `s` in `m`
on `t`. It has no unit in general: `V_! = m~`, and `m~ → V` is not an isomorphism unless
`m = V`. Its unitisation is
`R_!! = (V ⊕ R_!) ⧸ I`,
where `I` is spanned by the elements `(x * y, -(x ⊗ y) ⊗ 1)` for `x, y ∈ m` (Gabber–Ramero
§2.2). The span is already an ideal, and it is the image of the
`V`-linear map `m~ → V ⊕ R_!`, `t ↦ (t, -t ⊗ 1)`. The algebra `R` is called *exact* if this map
is injective, so that `0 → m~ → V ⊕ R_! → R_!! → 0` is exact; this holds for every `R`
when `m~ → m` is injective (Gabber–Ramero, Definition 2.2.25 and Remark 2.2.26).

The unitisation receives the natural `V`-algebra map `R_!! → R`, `(v, t ⊗ r) ↦ v + t • r`,
and this map is an almost isomorphism. For an almost algebra `B`, applying the construction to the
algebra `B_*` of almost elements gives the functor `B ↦ B_!!` from almost `V`-algebras to
commutative `V`-algebras, together with the natural map `B_!! → B_*` and the isomorphism
`B ≅ (B_!!)^a`. The construction is the input of the left adjoint `B ↦ B_!!` of
almostification on algebras and of the comparison of faithful flatness of `φ` and `φ_!!`.

## Main definitions

* `TauCeti.Almost.BasicSetup.Shriek`: the commutative non-unital `V`-algebra `R_! = m~ ⊗[V] R`,
  with the action map `TauCeti.Almost.BasicSetup.Shriek.act : R_! → R`.
* `TauCeti.Almost.BasicSetup.ShriekShriek`: the commutative `V`-algebra `R_!! = (V ⊕ R_!) ⧸ I`,
  a quotient of Mathlib's `Unitization V R_!`, with its universal property
  `TauCeti.Almost.BasicSetup.ShriekShriek.lift`.
* `TauCeti.Almost.BasicSetup.shriekShriekRel`: the map `m~ → V ⊕ R_!`, `t ↦ (t, -t ⊗ 1)`,
  whose image is the ideal `I`.
* `TauCeti.Almost.BasicSetup.IsShriekShriekExact`: exactness of `R`, injectivity of
  `shriekShriekRel`.
* `TauCeti.Almost.Algebra.IsExact`: exactness of an almost algebra `B`, exactness of `B_*`.
* `TauCeti.Almost.BasicSetup.shriekShriekCounit`: the `V`-algebra map `R_!! → R`.
* `TauCeti.Almost.BasicSetup.shriekShriekMap`: the map `R_!! → R'_!!` induced by `R → R'`.
* `TauCeti.Almost.Algebra.shriekShriek`: the functor `B ↦ B_!!` from almost `V`-algebras to
  commutative `V`-algebras, with `TauCeti.Almost.Algebra.shriekShriekToElements : B_!! → B_*`.
* `TauCeti.Almost.Algebra.shriekShriekUnitIso`: the natural isomorphism `B ≅ (B_!!)^a`.

## Main results

* `TauCeti.Almost.BasicSetup.restrictScalars_shriekShriekIdeal` and
  `TauCeti.Almost.BasicSetup.exact_shriekShriekRel`: the ideal `I` is the image of `m~`, so
  `m~ → V ⊕ R_! → R_!!` is exact.
* `TauCeti.Almost.BasicSetup.isAlmostIso_shriekShriekCounit`: `R_!! → R` is an almost
  isomorphism.
* `TauCeti.Almost.BasicSetup.shriekShriekMap_bijective_of_isAlmostIso`: an almost isomorphism
  `R → R'` induces an isomorphism `R_!! ≅ R'_!!`, so `R_!!` only depends on `R^a`.
* `TauCeti.Almost.BasicSetup.isShriekShriekExact_of_tildeMul_injective`: if `m~ → V` is
  injective, every algebra is exact, and so is every almost algebra
  (`TauCeti.Almost.Algebra.isExact_of_tildeMul_injective`);
  `TauCeti.Almost.BasicSetup.isShriekShriekExact_of_lTensor_injective`: so is every algebra `R`
  for which `t ↦ t ⊗ 1` is injective on `m~`.
* `TauCeti.Almost.BasicSetup.shriekShriekCounit_self_bijective`: `V_!! ≅ V`.

## References

* O. Gabber, L. Ramero, *Almost ring theory*, Lecture Notes in Mathematics 1800, §2.2,
  Definition 2.2.25, Remark 2.2.26 and Proposition 2.2.27.
* B. Bhatt, *Lecture notes for a class on perfectoid spaces*, §4.2, Remark 4.2.8.
-/

public section

universe u v w

open CategoryTheory TensorProduct

namespace TauCeti.Almost.BasicSetup

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-! ### The non-unital algebra `R_! = m~ ⊗[V] R` -/

section Shriek

variable (R : Type v) [CommRing R] [_root_.Algebra V R]

/-- The commutative non-unital `V`-algebra `R_! = m~ ⊗[V] R` of a commutative `V`-algebra `R`
(Gabber–Ramero §2.2). It is a type synonym for `m~ ⊗[V] R`, carrying the product
`(s ⊗ a) * (t ⊗ b) = (s * t) ⊗ (a * b)` described by `Shriek.tmul_mul_tmul`; `Shriek.equiv`
identifies `R_!` with `m~ ⊗[V] R`. -/
def Shriek : Type (max u v) :=
  S.tilde ⊗[V] R

noncomputable instance : AddCommGroup (S.Shriek R) :=
  inferInstanceAs (AddCommGroup (S.tilde ⊗[V] R))

noncomputable instance : _root_.Module V (S.Shriek R) :=
  inferInstanceAs (_root_.Module V (S.tilde ⊗[V] R))

namespace Shriek

/-- The identification of the underlying `V`-module of `R_!` with `m~ ⊗[V] R`. -/
noncomputable def equiv : S.tilde ⊗[V] R ≃ₗ[V] S.Shriek R :=
  LinearEquiv.refl V _

/-- The product of `R_!` as a bilinear map, `(s ⊗ a) (t ⊗ b) ↦ (s * t) ⊗ (a * b)`, where
`s * t = tildeMul s • t` is the product of `m~`, the action of the image of `s` in `V`
(`mulBilin_tmul`). -/
noncomputable def mulBilin : S.Shriek R →ₗ[V] S.Shriek R →ₗ[V] S.Shriek R :=
  TensorProduct.map₂ (LinearMap.lsmul V S.tilde ∘ₗ S.tildeMul) (LinearMap.mul V R)

theorem mulBilin_tmul (s t : S.tilde) (a b : R) :
    mulBilin S R (equiv S R (s ⊗ₜ a)) (equiv S R (t ⊗ₜ b)) =
      equiv S R ((S.tildeMul s • t) ⊗ₜ (a * b)) := by
  -- `equiv` is the identity of the type synonym `R_! = m~ ⊗[V] R`.
  change TensorProduct.map₂ (LinearMap.lsmul V S.tilde ∘ₗ S.tildeMul) (LinearMap.mul V R)
    (s ⊗ₜ a) (t ⊗ₜ b) = (S.tildeMul s • t) ⊗ₜ[V] (a * b)
  simp [TensorProduct.map₂_apply_tmul]

noncomputable instance : Mul (S.Shriek R) where
  mul x y := mulBilin S R x y

theorem mul_def (x y : S.Shriek R) : x * y = mulBilin S R x y :=
  (rfl)

/-- Induction principle for `R_!`: a property closed under addition and holding on pure
tensors holds everywhere. -/
@[elab_as_elim]
theorem induction_on {p : S.Shriek R → Prop} (x : S.Shriek R)
    (tmul : ∀ (t : S.tilde) (r : R), p (equiv S R (t ⊗ₜ r)))
    (add : ∀ x y, p x → p y → p (x + y)) : p x := by
  obtain ⟨x, rfl⟩ := (equiv S R).surjective x
  induction x using TensorProduct.inductionOn with
  | tmul t r => exact tmul t r
  | add x y hx hy => simpa using add _ _ hx hy

@[simp]
theorem tmul_mul_tmul (s t : S.tilde) (a b : R) :
    equiv S R (s ⊗ₜ a) * equiv S R (t ⊗ₜ b) = equiv S R ((S.tildeMul s • t) ⊗ₜ (a * b)) :=
  mulBilin_tmul S R s t a b

private theorem mul_assoc' (x y z : S.Shriek R) : x * y * z = x * (y * z) := by
  simp only [mul_def]
  induction x using induction_on with
  | add x x' hx hx' => simp [hx, hx']
  | tmul s a =>
    induction y using induction_on with
    | add y y' hy hy' => simp [hy, hy']
    | tmul t b =>
      induction z using induction_on with
      | add z z' hz hz' => simp [hz, hz']
      | tmul u c =>
        simp only [mulBilin_tmul, map_smul, smul_smul, mul_assoc, smul_eq_mul]

private theorem mul_comm' (x y : S.Shriek R) : x * y = y * x := by
  simp only [mul_def]
  induction x using induction_on with
  | add x x' hx hx' => simp [hx, hx']
  | tmul s a =>
    induction y using induction_on with
    | add y y' hy hy' => simp [hy, hy']
    | tmul t b => rw [mulBilin_tmul, mulBilin_tmul, tildeMul_smul_comm, mul_comm a]

noncomputable instance : NonUnitalCommRing (S.Shriek R) where
  left_distrib x y z := map_add (mulBilin S R x) y z
  right_distrib x y z := LinearMap.map_add₂ (mulBilin S R) x y z
  zero_mul x := LinearMap.map_zero₂ (mulBilin S R) x
  mul_zero x := map_zero (mulBilin S R x)
  mul_assoc x y z := by exact mul_assoc' S R x y z
  mul_comm x y := by exact mul_comm' S R x y

instance : IsScalarTower V (S.Shriek R) (S.Shriek R) :=
  ⟨fun v x y ↦ LinearMap.map_smul₂ (mulBilin S R) v x y⟩

instance : SMulCommClass V (S.Shriek R) (S.Shriek R) :=
  ⟨fun v x y ↦ (map_smul (mulBilin S R x) v y).symm⟩

/-- Right multiplication by `t ⊗ 1` on `R_!` is the action of `t ∈ m~` through `m~ → V`. -/
theorem mul_tmul_one (z : S.Shriek R) (t : S.tilde) :
    z * equiv S R (t ⊗ₜ 1) = S.tildeMul t • z := by
  induction z using induction_on with
  | add z z' hz hz' => rw [add_mul, hz, hz', smul_add]
  | tmul s a =>
    rw [tmul_mul_tmul, mul_one, tildeMul_smul_comm, ← map_smul, smul_tmul']

/-- A linear map from `R_!` to a non-unital algebra is multiplicative as soon as it is
multiplicative on pure tensors. -/
private theorem map_mul_of_tmul {A : Type*} [NonUnitalNonAssocSemiring A] [_root_.Module V A]
    (g : S.Shriek R →ₗ[V] A)
    (h : ∀ (s t : S.tilde) (a b : R), g (equiv S R (s ⊗ₜ a) * equiv S R (t ⊗ₜ b)) =
      g (equiv S R (s ⊗ₜ a)) * g (equiv S R (t ⊗ₜ b))) (x y : S.Shriek R) :
    g (x * y) = g x * g y := by
  induction x using induction_on with
  | add x x' hx hx' => rw [add_mul, map_add, map_add, hx, hx', add_mul]
  | tmul s a =>
    induction y using induction_on with
    | add y y' hy hy' => rw [mul_add, map_add, map_add, hy, hy', mul_add]
    | tmul t b => exact h s t a b

variable {R} {R' : Type w} [CommRing R'] [_root_.Algebra V R']

/-- A `V`-algebra map `f : R → R'` induces the non-unital algebra map `R_! → R'_!`,
`t ⊗ r ↦ t ⊗ f r`. -/
noncomputable def map (f : R →ₐ[V] R') : S.Shriek R →ₙₐ[V] S.Shriek R' where
  __ := (equiv S R').toLinearMap ∘ₗ f.toLinearMap.lTensor S.tilde ∘ₗ (equiv S R).symm.toLinearMap
  map_zero' := map_zero _
  map_mul' := map_mul_of_tmul S R _ fun s t a b ↦ by
    simp only [tmul_mul_tmul, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, LinearMap.lTensor_tmul, AlgHom.toLinearMap_apply, map_mul]

theorem map_apply (f : R →ₐ[V] R') (z : S.Shriek R) :
    map S f z = equiv S R' (f.toLinearMap.lTensor S.tilde ((equiv S R).symm z)) :=
  (rfl)

@[simp]
theorem map_tmul (f : R →ₐ[V] R') (t : S.tilde) (r : R) :
    map S f (equiv S R (t ⊗ₜ r)) = equiv S R' (t ⊗ₜ f r) := by
  -- `equiv` is the identity of the type synonym `R_! = m~ ⊗[V] R`.
  change f.toLinearMap.lTensor S.tilde (t ⊗ₜ r) = t ⊗ₜ[V] f r
  simp [LinearMap.lTensor_tmul]

variable (R) in
/-- The action map `R_! = m~ ⊗[V] R → R`, `t ⊗ r ↦ t • r`, as a non-unital algebra map. -/
noncomputable def act : S.Shriek R →ₙₐ[V] R where
  __ := S.tildeAct R ∘ₗ (equiv S R).symm.toLinearMap
  map_zero' := map_zero _
  map_mul' := map_mul_of_tmul S R _ fun s t a b ↦ by
    simp only [tmul_mul_tmul, LinearMap.coe_comp, LinearEquiv.coe_coe, Function.comp_apply,
      LinearEquiv.symm_apply_apply, tildeAct_tmul, map_smul, smul_eq_mul, smul_mul_smul_comm,
      mul_smul]

theorem act_apply (z : S.Shriek R) :
    act S R z = S.tildeAct R ((equiv S R).symm z) :=
  (rfl)

@[simp]
theorem act_tmul (t : S.tilde) (r : R) :
    act S R (equiv S R (t ⊗ₜ r)) = S.tildeMul t • r :=
  S.tildeAct_tmul R t r

/-- The action map is natural in the algebra. -/
theorem act_map (f : R →ₐ[V] R') (z : S.Shriek R) :
    act S R' (map S f z) = f (act S R z) := by
  induction z using induction_on with
  | add z z' hz hz' => simp only [map_add, hz, hz']
  | tmul t r => simp

end Shriek

end Shriek

/-! ### The unitisation `R_!! = (V ⊕ R_!) ⧸ I` -/

section ShriekShriek

variable (R : Type v) [CommRing R] [_root_.Algebra V R]

open Shriek

/-- The `V`-linear map `m~ → V ⊕ R_!`, `t ↦ (t, -t ⊗ 1)`, where `t` acts on `V` through the
multiplication `m~ → V`. Its image is the ideal of relations of `R_!!`
(`restrictScalars_shriekShriekIdeal`). -/
noncomputable def shriekShriekRel : S.tilde →ₗ[V] Unitization V (S.Shriek R) where
  toFun t := Unitization.inl (S.tildeMul t) - (equiv S R (t ⊗ₜ 1) : Unitization V (S.Shriek R))
  map_add' s t := by
    simp only [map_add, add_tmul, Unitization.inl_add, Unitization.inr_add]
    abel
  map_smul' v t := by
    simp [smul_sub, ← smul_tmul', Unitization.inl_smul, -smul_eq_mul]

theorem shriekShriekRel_apply (t : S.tilde) :
    S.shriekShriekRel R t =
      Unitization.inl (S.tildeMul t) - (equiv S R (t ⊗ₜ 1) : Unitization V (S.Shriek R)) :=
  (rfl)

@[simp]
theorem fst_shriekShriekRel (t : S.tilde) : (S.shriekShriekRel R t).fst = S.tildeMul t := by
  simp [shriekShriekRel_apply, sub_eq_add_neg, ← Unitization.inr_neg]

@[simp]
theorem snd_shriekShriekRel (t : S.tilde) :
    (S.shriekShriekRel R t).snd = -equiv S R (t ⊗ₜ 1) := by
  simp [shriekShriekRel_apply, sub_eq_add_neg, ← Unitization.inr_neg]

/-- The relations `x * (t, -t ⊗ 1) = (x₀ t, -(x₀ t) ⊗ 1)` for `x = (x₀, z)`: multiplying a relation
by an element of `V ⊕ R_!` only rescales it by the scalar part (Gabber–Ramero §2.2). -/
theorem mul_shriekShriekRel (x : Unitization V (S.Shriek R)) (t : S.tilde) :
    x * S.shriekShriekRel R t = S.shriekShriekRel R (x.fst • t) := by
  ext
  · simp
  · simp [mul_tmul_one]

/-- The ideal `I` of relations of `R_!!`, spanned by the elements `(t, -t ⊗ 1)` for `t ∈ m~`. -/
noncomputable def shriekShriekIdeal : Ideal (Unitization V (S.Shriek R)) :=
  Ideal.span (Set.range (S.shriekShriekRel R))

theorem shriekShriekRel_mem_shriekShriekIdeal (t : S.tilde) :
    S.shriekShriekRel R t ∈ S.shriekShriekIdeal R :=
  Ideal.subset_span ⟨t, rfl⟩

/-- **The ideal of relations of `R_!!` is the image of `m~`**: the `V`-span of the elements
`(t, -t ⊗ 1)` is already an ideal of `V ⊕ R_!` (Gabber–Ramero §2.2). -/
theorem restrictScalars_shriekShriekIdeal :
    (S.shriekShriekIdeal R).restrictScalars V = LinearMap.range (S.shriekShriekRel R) := by
  refine le_antisymm (fun x hx ↦ ?_) ?_
  · rw [Submodule.restrictScalars_mem] at hx
    induction hx using Submodule.span_induction with
    | mem _ hx => exact LinearMap.mem_range.mpr (Set.mem_range.mp hx)
    | zero => exact zero_mem _
    | add x y _ _ hx hy => exact add_mem hx hy
    | smul a x _ hx =>
      obtain ⟨t, rfl⟩ := LinearMap.mem_range.mp hx
      exact LinearMap.mem_range.mpr ⟨a.fst • t, (S.mul_shriekShriekRel R a t).symm⟩
  · rintro _ ⟨t, rfl⟩
    exact S.shriekShriekRel_mem_shriekShriekIdeal R t

theorem mem_shriekShriekIdeal_iff {x : Unitization V (S.Shriek R)} :
    x ∈ S.shriekShriekIdeal R ↔ ∃ t, S.shriekShriekRel R t = x := by
  rw [← Submodule.restrictScalars_mem V, restrictScalars_shriekShriekIdeal, LinearMap.mem_range]

/-- The **unitisation `R_!! = (V ⊕ R_!) ⧸ I`** of the non-unital algebra `R_! = m~ ⊗[V] R`, where
`I` is spanned by the elements `(x * y, -(x ⊗ y) ⊗ 1)` for `x, y ∈ m` (Gabber–Ramero §2.2). It is a
commutative `V`-algebra with an almost isomorphism `R_!! → R` (`isAlmostIso_shriekShriekCounit`). -/
def ShriekShriek : Type (max u v) :=
  Unitization V (S.Shriek R) ⧸ S.shriekShriekIdeal R

noncomputable instance : CommRing (S.ShriekShriek R) :=
  inferInstanceAs (CommRing (Unitization V (S.Shriek R) ⧸ S.shriekShriekIdeal R))

noncomputable instance : _root_.Algebra V (S.ShriekShriek R) :=
  inferInstanceAs (_root_.Algebra V (Unitization V (S.Shriek R) ⧸ S.shriekShriekIdeal R))

namespace ShriekShriek

/-- The quotient map `V ⊕ R_! → R_!!`. -/
noncomputable def mk : Unitization V (S.Shriek R) →ₐ[V] S.ShriekShriek R :=
  Ideal.Quotient.mkₐ V (S.shriekShriekIdeal R)

theorem mk_surjective : Function.Surjective (mk S R) :=
  Ideal.Quotient.mkₐ_surjective V _

theorem mk_eq_zero_iff {x : Unitization V (S.Shriek R)} :
    mk S R x = 0 ↔ x ∈ S.shriekShriekIdeal R :=
  Ideal.Quotient.eq_zero_iff_mem

/-- The non-unital algebra map `R_! → R_!!`, `z ↦ (0, z)`. -/
noncomputable def inr : S.Shriek R →ₙₐ[V] S.ShriekShriek R :=
  (mk S R).toNonUnitalAlgHom.comp (Unitization.inrNonUnitalAlgHom V (S.Shriek R))

theorem inr_apply (z : S.Shriek R) : inr S R z = mk S R (z : Unitization V (S.Shriek R)) :=
  (rfl)

@[simp]
theorem mk_inl (v : V) : mk S R (Unitization.inl v) = algebraMap V (S.ShriekShriek R) v := by
  rw [← Unitization.algebraMap_eq_inl, AlgHom.commutes]

/-- In `R_!!`, the element `t ⊗ 1` of `R_!` is identified with the scalar `t ∈ m~ → V`. -/
@[simp]
theorem inr_tmul_one (t : S.tilde) :
    inr S R (equiv S R (t ⊗ₜ 1)) = algebraMap V (S.ShriekShriek R) (S.tildeMul t) := by
  -- The relation `(t, -t ⊗ 1)` maps to zero in `R_!!`.
  have := (mk_eq_zero_iff S R).mpr (S.shriekShriekRel_mem_shriekShriekIdeal R t)
  rw [shriekShriekRel_apply, map_sub, mk_inl, sub_eq_zero] at this
  exact this.symm

/-- Every element of `R_!!` is the sum of a scalar and an element of `R_!`. -/
theorem exists_eq_algebraMap_add_inr (x : S.ShriekShriek R) :
    ∃ v z, algebraMap V (S.ShriekShriek R) v + inr S R z = x := by
  obtain ⟨x, rfl⟩ := mk_surjective S R x
  exact ⟨x.fst, x.snd, by rw [inr_apply, ← mk_inl, ← map_add, Unitization.inl_fst_add_inr_snd_eq]⟩

end ShriekShriek

/-- **The sequence `m~ → V ⊕ R_! → R_!!` is exact**: the kernel of the quotient map is the image of
`m~`. Together with injectivity on the left (`IsShriekShriekExact`) and the surjectivity of the
quotient map, this gives the exact sequence `0 → m~ → V ⊕ R_! → R_!! → 0` of Gabber–Ramero,
Definition 2.2.25. -/
theorem exact_shriekShriekRel : Function.Exact (S.shriekShriekRel R) (ShriekShriek.mk S R) := by
  intro x
  rw [ShriekShriek.mk_eq_zero_iff, mem_shriekShriekIdeal_iff, Set.mem_range]

namespace ShriekShriek

variable {S R}

/-- Two `V`-algebra maps out of `R_!!` agree if they agree on the elements `t ⊗ r` of `R_!`. -/
@[ext]
theorem algHom_ext {A : Type*} [Semiring A] [_root_.Algebra V A]
    {φ ψ : S.ShriekShriek R →ₐ[V] A}
    (h : ∀ (t : S.tilde) (r : R), φ (inr S R (equiv S R (t ⊗ₜ r))) =
      ψ (inr S R (equiv S R (t ⊗ₜ r)))) : φ = ψ := by
  have h' (z : S.Shriek R) : φ (inr S R z) = ψ (inr S R z) := by
    induction z using Shriek.induction_on with
    | add z z' hz hz' => rw [map_add, map_add, map_add, hz, hz']
    | tmul t r => exact h t r
  refine AlgHom.ext fun x ↦ ?_
  obtain ⟨v, z, rfl⟩ := exists_eq_algebraMap_add_inr S R x
  rw [map_add, map_add, AlgHom.commutes, AlgHom.commutes, h']

section lift

variable {A : Type*} [Semiring A] [_root_.Algebra V A] (f : S.Shriek R →ₙₐ[V] A)

/-- The extension `V ⊕ R_! → A`, `(v, z) ↦ v + f z`, of `f` kills the ideal of relations `I`. -/
private theorem unitization_lift_eq_zero
    (hf : ∀ t, f (equiv S R (t ⊗ₜ 1)) = algebraMap V A (S.tildeMul t))
    (x : Unitization V (S.Shriek R)) (hx : x ∈ S.shriekShriekIdeal R) :
    Unitization.lift f x = 0 := by
  obtain ⟨t, rfl⟩ := (S.mem_shriekShriekIdeal_iff R).mp hx
  have : f (equiv S R (t ⊗ₜ 1)) + f (-equiv S R (t ⊗ₜ 1)) = 0 := by
    rw [← map_add, add_neg_cancel, map_zero]
  simpa [hf] using this

/-- The **universal property of `R_!!`**: a non-unital `V`-algebra map `f : R_! → A` that sends
each `t ⊗ 1` to the scalar `t ∈ m~ → V` extends uniquely (`algHom_ext`) to a `V`-algebra map
`R_!! → A`, `(v, z) ↦ v + f z`. -/
noncomputable def lift (hf : ∀ t, f (equiv S R (t ⊗ₜ 1)) = algebraMap V A (S.tildeMul t)) :
    S.ShriekShriek R →ₐ[V] A :=
  Ideal.Quotient.liftₐ (S.shriekShriekIdeal R) (Unitization.lift f)
    (unitization_lift_eq_zero f hf)

@[simp]
theorem lift_mk (hf : ∀ t, f (equiv S R (t ⊗ₜ 1)) = algebraMap V A (S.tildeMul t))
    (x : Unitization V (S.Shriek R)) :
    lift f hf (mk S R x) = algebraMap V A x.fst + f x.snd := by
  -- `Ideal.Quotient.liftₐ_comp`, stated for the type synonym `R_!!` of the quotient.
  have h : (lift f hf).comp (mk S R) = Unitization.lift f :=
    Ideal.Quotient.liftₐ_comp _ _ (unitization_lift_eq_zero f hf)
  simpa using DFunLike.congr_fun h x

@[simp]
theorem lift_inr (hf : ∀ t, f (equiv S R (t ⊗ₜ 1)) = algebraMap V A (S.tildeMul t))
    (z : S.Shriek R) : lift f hf (inr S R z) = f z := by
  rw [inr_apply, lift_mk, Unitization.fst_inr, map_zero, zero_add, Unitization.snd_inr]

end lift

end ShriekShriek

/-! ### Exactness -/

/-- A `V`-algebra `R` is **exact** if `m~ → V ⊕ R_!`, `t ↦ (t, -t ⊗ 1)`, is injective, so that
`0 → m~ → V ⊕ R_! → R_!! → 0` is exact (`exact_shriekShriekRel`; Gabber–Ramero, Definition
2.2.25). An almost algebra `B` is exact when its algebra `B_*` of almost elements is
(`TauCeti.Almost.Algebra.IsExact`). -/
def IsShriekShriekExact : Prop :=
  Function.Injective (S.shriekShriekRel R)

theorem isShriekShriekExact_iff :
    S.IsShriekShriekExact R ↔ Function.Injective (S.shriekShriekRel R) :=
  Iff.rfl

/-- If `m~ → V` is injective (for instance if `m` is flat), every `V`-algebra is exact
(Gabber–Ramero, Remark 2.2.26). -/
theorem isShriekShriekExact_of_tildeMul_injective (h : Function.Injective S.tildeMul) :
    S.IsShriekShriekExact R := by
  refine (S.isShriekShriekExact_iff R).mpr <| (injective_iff_map_eq_zero _).mpr fun t ht ↦ h ?_
  simpa using congrArg (·.fst) ht

/-- If `t ↦ t ⊗ 1` is injective on `m~`, then `R` is exact. -/
theorem isShriekShriekExact_of_lTensor_injective
    (h : Function.Injective ((Algebra.linearMap V R).lTensor S.tilde)) :
    S.IsShriekShriekExact R := by
  refine (S.isShriekShriekExact_iff R).mpr <| (injective_iff_map_eq_zero _).mpr fun t ht ↦ ?_
  have h₂ : equiv S R (t ⊗ₜ[V] (1 : R)) = 0 := by
    simpa using congrArg (·.snd) ht
  rw [LinearEquiv.map_eq_zero_iff] at h₂
  refine (TensorProduct.rid V S.tilde).symm.injective (h ?_)
  simpa using h₂

/-! ### The counit `R_!! → R` -/

/-- The **natural `V`-algebra map `R_!! → R`**, `(v, t ⊗ r) ↦ v + t • r`, an almost isomorphism
(`isAlmostIso_shriekShriekCounit`). -/
noncomputable def shriekShriekCounit : S.ShriekShriek R →ₐ[V] R :=
  ShriekShriek.lift (Shriek.act S R) fun t ↦ by rw [act_tmul, Algebra.algebraMap_eq_smul_one]

@[simp]
theorem shriekShriekCounit_mk (x : Unitization V (S.Shriek R)) :
    S.shriekShriekCounit R (ShriekShriek.mk S R x) =
      algebraMap V R x.fst + Shriek.act S R x.snd :=
  ShriekShriek.lift_mk _ _ x

@[simp]
theorem shriekShriekCounit_inr (z : S.Shriek R) :
    S.shriekShriekCounit R (ShriekShriek.inr S R z) = Shriek.act S R z :=
  ShriekShriek.lift_inr _ _ z

theorem shriekShriekCounit_tmul (t : S.tilde) (r : R) :
    S.shriekShriekCounit R (ShriekShriek.inr S R (equiv S R (t ⊗ₜ r))) = S.tildeMul t • r := by
  simp

/-- The kernel of the action map `R_! → R` is almost zero. -/
private theorem smul_eq_zero_of_act_eq_zero {ε : V} (hε : ε ∈ S.ideal) {z : S.Shriek R}
    (hz : Shriek.act S R z = 0) : ε • z = 0 := by
  -- Instance search does not find the `AddCommGroup` structure on the kernel of a map out of a
  -- tensor product, so it is supplied by hand.
  let _ : AddCommGroup (LinearMap.ker (S.tildeAct R)) :=
    Submodule.addCommGroup (M := S.tilde ⊗[V] R) _
  have h := (isAlmostIso_iff.mp (S.isAlmostIso_tildeAct R)).1.smul_eq_zero hε
    ⟨(equiv S R).symm z, by rwa [LinearMap.mem_ker, ← Shriek.act_apply]⟩
  rw [Subtype.ext_iff, Submodule.coe_smul, Submodule.coe_zero] at h
  exact (equiv S R).symm.map_eq_zero_iff.mp ((map_smul _ ε z).trans h)

/-- The kernel of `R_!! → R` is almost zero: for `ε, δ ∈ m`, the product `δ ε` kills it. -/
private theorem smul_eq_zero_of_shriekShriekCounit_eq_zero {ε : V} (hε : ε ∈ S.ideal)
    {x : S.ShriekShriek R} (hx : S.shriekShriekCounit R x = 0) : ε • x = 0 := by
  obtain ⟨v, z, rfl⟩ := ShriekShriek.exists_eq_algebraMap_add_inr S R x
  refine S.mul_induction_on (p := (· • (algebraMap V _ v + ShriekShriek.inr S R z) = 0)) hε
    (fun δ hδ ε hε ↦ ?_) fun a b ha hb ↦ by
      rw [add_smul, ha, hb, add_zero]
  -- `ε = t` for some `t ∈ m~`, and `ε • (v, z) = (0, ε • z + t ⊗ v)` in `R_!!`, where
  -- `ε • z + t ⊗ v` lies in the kernel of `R_! → R`, which `δ` kills.
  obtain ⟨t, rfl⟩ := S.exists_tildeMul_eq hε
  have hw : S.tildeMul t • (algebraMap V _ v + ShriekShriek.inr S R z) =
      ShriekShriek.inr S R (S.tildeMul t • z + equiv S R (t ⊗ₜ algebraMap V R v)) := by
    simp only [Algebra.algebraMap_eq_smul_one, tmul_smul, map_add, map_smul,
      ShriekShriek.inr_tmul_one, smul_add]
    module
  have hw₀ : Shriek.act S R (S.tildeMul t • z + equiv S R (t ⊗ₜ algebraMap V R v)) = 0 := by
    simp only [map_add, AlgHom.commutes, shriekShriekCounit_inr] at hx
    simp only [map_add, map_smul, act_tmul, Algebra.smul_def]
    linear_combination algebraMap V R (S.tildeMul t) * hx
  rw [mul_smul, hw, ← map_smul, smul_eq_zero_of_act_eq_zero S R hδ hw₀, map_zero]

/-- **The natural map `R_!! → R` is an almost isomorphism** (Gabber–Ramero §2.2; Bhatt, Remark
4.2.8). -/
theorem isAlmostIso_shriekShriekCounit :
    S.IsAlmostIso (S.shriekShriekCounit R).toLinearMap := by
  refine isAlmostIso_iff.mpr ⟨isAlmostZero_iff.mpr fun ε hε x ↦ Subtype.ext ?_,
    isAlmostZero_iff.mpr fun ε hε x ↦ ?_⟩
  · rw [Submodule.coe_smul, Submodule.coe_zero]
    exact S.smul_eq_zero_of_shriekShriekCounit_eq_zero R hε
      ((AlgHom.toLinearMap_apply _ _).symm.trans (LinearMap.mem_ker.mp x.property))
  · obtain ⟨x, rfl⟩ := Submodule.mkQ_surjective _ x
    obtain ⟨t, rfl⟩ := S.exists_tildeMul_eq hε
    rw [← map_smul, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
    exact LinearMap.mem_range.mpr
      ⟨ShriekShriek.inr S R (equiv S R (t ⊗ₜ x)), by simp⟩

/-- For `R = V`, the natural map `V_!! → V` is bijective: `V_! = m~` and
`(V ⊕ m~) ⧸ I ≅ V`, `(v, t) ↦ v + t` (Gabber–Ramero §2.2). -/
theorem shriekShriekCounit_self_bijective : Function.Bijective (S.shriekShriekCounit V) := by
  -- Over `V`, every element of `V_!` is identified in `V_!!` with a scalar.
  have hz (z : S.Shriek V) : ShriekShriek.inr S V z =
      algebraMap V (S.ShriekShriek V) (Shriek.act S V z) := by
    induction z using Shriek.induction_on with
    | add z z' hz hz' => rw [map_add, map_add, hz, hz', map_add]
    | tmul t a =>
      have : t ⊗ₜ[V] a = a • t ⊗ₜ[V] (1 : V) := by rw [smul_tmul', smul_tmul, smul_eq_mul, mul_one]
      simp [this, Algebra.smul_def, mul_comm]
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun v ↦ ⟨algebraMap V _ v, by simp⟩⟩
  obtain ⟨v, z, rfl⟩ := ShriekShriek.exists_eq_algebraMap_add_inr S V x
  rw [hz, ← map_add] at hx ⊢
  rw [AlgHom.commutes, Algebra.algebraMap_self, RingHom.id_apply] at hx
  rw [hx, map_zero]

end ShriekShriek

/-! ### Functoriality -/

section Functoriality

variable {R : Type v} [CommRing R] [_root_.Algebra V R] {R' : Type w} [CommRing R']
  [_root_.Algebra V R'] {R'' : Type*} [CommRing R''] [_root_.Algebra V R'']

open Shriek

/-- A `V`-algebra map `f : R → R'` induces the `V`-algebra map `R_!! → R'_!!`,
`(v, t ⊗ r) ↦ (v, t ⊗ f r)`. -/
noncomputable def shriekShriekMap (f : R →ₐ[V] R') : S.ShriekShriek R →ₐ[V] S.ShriekShriek R' :=
  ShriekShriek.lift ((ShriekShriek.inr S R').comp (Shriek.map S f)) fun t ↦ by
    rw [NonUnitalAlgHom.comp_apply, Shriek.map_tmul, map_one, ShriekShriek.inr_tmul_one]

@[simp]
theorem shriekShriekMap_mk (f : R →ₐ[V] R') (x : Unitization V (S.Shriek R)) :
    S.shriekShriekMap f (ShriekShriek.mk S R x) =
      ShriekShriek.mk S R' (Unitization.map (Shriek.map S f) x) := by
  rw [shriekShriekMap, ShriekShriek.lift_mk, NonUnitalAlgHom.comp_apply, ShriekShriek.inr_apply,
    ← ShriekShriek.mk_inl, ← map_add]
  congr 1
  ext <;> simp

@[simp]
theorem shriekShriekMap_inr (f : R →ₐ[V] R') (z : S.Shriek R) :
    S.shriekShriekMap f (ShriekShriek.inr S R z) = ShriekShriek.inr S R' (Shriek.map S f z) := by
  rw [shriekShriekMap, ShriekShriek.lift_inr, NonUnitalAlgHom.comp_apply]

@[simp]
theorem shriekShriekMap_id : S.shriekShriekMap (AlgHom.id V R) = AlgHom.id V _ := by
  ext; simp

theorem shriekShriekMap_comp (g : R' →ₐ[V] R'') (f : R →ₐ[V] R') :
    S.shriekShriekMap (g.comp f) = (S.shriekShriekMap g).comp (S.shriekShriekMap f) := by
  ext; simp

/-- The natural map `R_!! → R` is natural in `R`. -/
theorem shriekShriekCounit_comp_shriekShriekMap (f : R →ₐ[V] R') :
    (S.shriekShriekCounit R').comp (S.shriekShriekMap f) = f.comp (S.shriekShriekCounit R) := by
  ext; simp

/-- **`R_!!` only depends on `R^a`**: if `f : R → R'` is an almost isomorphism, then
`R_!! → R'_!!` is bijective, as `m~ ⊗[V] f` is. -/
theorem shriekShriekMap_bijective_of_isAlmostIso {f : R →ₐ[V] R'}
    (hf : S.IsAlmostIso f.toLinearMap) : Function.Bijective (S.shriekShriekMap f) := by
  have hb : Function.Bijective (Shriek.map S f) := by
    rw [show ⇑(Shriek.map S f) = equiv S R' ∘ f.toLinearMap.lTensor S.tilde ∘ (equiv S R).symm
      from funext (Shriek.map_apply S f)]
    exact (equiv S R').bijective.comp (hf.lTensor_bijective.comp (equiv S R).symm.bijective)
  refine ⟨(injective_iff_map_eq_zero _).mpr fun x hx ↦ ?_, fun y ↦ ?_⟩
  · obtain ⟨x, rfl⟩ := ShriekShriek.mk_surjective S R x
    -- `x = (v, z)` maps to the relation `(t, -t ⊗ 1)` of `R'_!!`, so `z = -t ⊗ 1` already in `R_!`.
    rw [shriekShriekMap_mk, ShriekShriek.mk_eq_zero_iff, mem_shriekShriekIdeal_iff] at hx
    obtain ⟨t, ht⟩ := hx
    have h₁ : S.tildeMul t = x.fst := by simpa using congrArg (·.fst) ht
    have h₂ : Shriek.map S f x.snd = Shriek.map S f (-equiv S R (t ⊗ₜ 1)) := by
      simpa [eq_comm] using congrArg (·.snd) ht
    rw [ShriekShriek.mk_eq_zero_iff, mem_shriekShriekIdeal_iff]
    exact ⟨t, Unitization.ext (by simpa using h₁) (by simpa using (hb.1 h₂).symm)⟩
  · obtain ⟨v, z, rfl⟩ := ShriekShriek.exists_eq_algebraMap_add_inr S R' y
    obtain ⟨z, rfl⟩ := hb.2 z
    exact ⟨algebraMap V _ v + ShriekShriek.inr S R z, by simp⟩

end Functoriality

end TauCeti.Almost.BasicSetup

namespace TauCeti.Almost.Algebra

open BasicSetup

variable {V : Type u} [CommRing V] (S : BasicSetup V)

/-- The functor **`B ↦ B_!!`** from almost `V`-algebras to commutative `V`-algebras: the
unitisation `(B_*)_!! = (V ⊕ m~ ⊗[V] B_*) ⧸ I` of the non-unital algebra `B_! = m~ ⊗[V] B_*`
(Gabber–Ramero §2.2). The algebra `B` is recovered as `(B_!!)^a` (`shriekShriekUnitIso`). -/
@[expose]
noncomputable def shriekShriek : Algebra S ⥤ CommAlgCat.{u} V where
  obj B := CommAlgCat.of V (S.ShriekShriek ((elements S).obj B))
  map f := CommAlgCat.ofHom (S.shriekShriekMap ((elements S).map f).hom)
  map_id B := by ext1; simp
  map_comp f g := by ext1; simp [shriekShriekMap_comp]

/-- The natural map `B_!! → B_*`, `(v, t ⊗ b) ↦ v + t • b`, an almost isomorphism
(`isIso_toAlmost_map_shriekShriekToElements_app`). -/
@[expose]
noncomputable def shriekShriekToElements : shriekShriek S ⟶ elements S where
  app B := CommAlgCat.ofHom (X := S.ShriekShriek ((elements S).obj B)) (Y := (elements S).obj B)
    (S.shriekShriekCounit ((elements S).obj B))
  naturality B B' f := by
    ext1
    exact S.shriekShriekCounit_comp_shriekShriekMap ((elements S).map f).hom

theorem shriekShriek_obj (B : Algebra S) :
    (shriekShriek S).obj B = CommAlgCat.of V (S.ShriekShriek ((elements S).obj B)) :=
  (rfl)

@[simp]
theorem shriekShriek_map_hom {B B' : Algebra S} (f : B ⟶ B') :
    ((shriekShriek S).map f).hom = S.shriekShriekMap ((elements S).map f).hom :=
  (rfl)

@[simp]
theorem shriekShriekToElements_app_hom (B : Algebra S) :
    ((shriekShriekToElements S).app B).hom = S.shriekShriekCounit ((elements S).obj B) :=
  (rfl)

/-- The natural map `B_!! → B_*` becomes an isomorphism after almostification. -/
instance isIso_toAlmost_map_shriekShriekToElements_app (B : Algebra S) :
    IsIso ((toAlmost S).map ((shriekShriekToElements S).app B)) :=
  (isIso_toAlmost_map_iff S _).mpr <| by
    rw [shriekShriekToElements_app_hom]
    exact S.isAlmostIso_shriekShriekCounit ((elements S).obj B)

instance : IsIso (Functor.whiskerRight (shriekShriekToElements S) (toAlmost S)) :=
  have (B : Algebra S) :
      IsIso ((Functor.whiskerRight (shriekShriekToElements S) (toAlmost S)).app B) := by
    rw [Functor.whiskerRight_app]; infer_instance
  NatIso.isIso_of_isIso_app _

/-- **Every almost algebra is the almostification of its unitisation**: the natural isomorphism
`B ≅ (B_!!)^a`, composed of the counit isomorphism `B ≅ (B_*)^a` and the inverse of the
almostification of `B_!! → B_*` (Gabber–Ramero §2.2, Proposition 2.2.27). -/
noncomputable def shriekShriekUnitIso : 𝟭 (Algebra S) ≅ shriekShriek S ⋙ toAlmost S :=
  (counitIso S).symm ≪≫ (asIso (Functor.whiskerRight (shriekShriekToElements S) (toAlmost S))).symm

variable {S} in
/-- An almost `V`-algebra `B` is **exact** if its algebra `B_*` of almost elements is
(`IsShriekShriekExact`; Gabber–Ramero, Definition 2.2.25). -/
def IsExact (B : Algebra S) : Prop :=
  S.IsShriekShriekExact ((elements S).obj B)

theorem isExact_iff (B : Algebra S) : B.IsExact ↔ S.IsShriekShriekExact ((elements S).obj B) :=
  Iff.rfl

/-- If `m~ → V` is injective, every almost `V`-algebra is exact (Gabber–Ramero, Remark 2.2.26). -/
theorem isExact_of_tildeMul_injective (h : Function.Injective S.tildeMul) (B : Algebra S) :
    B.IsExact :=
  S.isShriekShriekExact_of_tildeMul_injective _ h

@[simp]
theorem shriekShriekUnitIso_inv_app (B : Algebra S) :
    (shriekShriekUnitIso S).inv.app B =
      (toAlmost S).map ((shriekShriekToElements S).app B) ≫ (adj S).counit.app B := by
  simp [shriekShriekUnitIso, counitIso_hom]

@[simp]
theorem shriekShriekUnitIso_hom_app (B : Algebra S) :
    (shriekShriekUnitIso S).hom.app B =
      (counitIso S).inv.app B ≫ inv ((toAlmost S).map ((shriekShriekToElements S).app B)) := by
  simp [shriekShriekUnitIso]

end TauCeti.Almost.Algebra
