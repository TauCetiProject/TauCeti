/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import TauCeti.Algebra.Module.Submodule.Pointwise
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Gluing
public import TauCeti.RingTheory.IntegralOrder.Basic
public import TauCeti.RingTheory.TensorProduct.Maps
import Mathlib.RingTheory.DedekindDomain.Factorization
import TauCeti.Algebra.Module.Lattice
import TauCeti.LinearAlgebra.TensorProduct.Tower

/-!
# Finite ideles of an order and the lattices they define

Let `A` be a Dedekind domain with fraction field `F`, let `B` be an `F`-algebra (not necessarily
commutative), and let `Λ` be an `A`-subalgebra of `B` spanning `B` over `F`, for instance an
`A`-order in `B`. For a height-one prime `v` of `A` write `𝒪_v` for the ring of integers of the
completion `F_v`. We take `B_v = 𝒪_v ⊗[A] B` as the completion of `B` at `v`: since every nonzero
element of `A` acts invertibly on `B`, it is canonically `F_v ⊗[F] B`. The completion of `Λ` is
its image `Λ_v = 𝒪_v Λ` in `B_v`, the `𝒪_v`-subalgebra `Subalgebra.baseChange 𝒪_v Λ`.

The finite idele group `J_f(Λ)` is the restricted product of the unit groups `B_vˣ` with respect
to the unit groups `Λ_vˣ`, and `U_f(Λ) ⊆ J_f(Λ)` is the subgroup of ideles with every component
in `Λ_vˣ`. Units of `B` map diagonally to `J_f(Λ)`.

To a finite idele `α` we attach the right `Λ`-lattice `I(α) = B ∩ ∏_v α_v Λ_v`
(`TauCeti.OrderIdeles.lattice`), glued from the local lattices `α_v Λ_v` with
`TauCeti.glueCompletions`. Its completion at every `v` is exactly `α_v Λ_v`; `I(α) = I(β)` exactly
when `α U_f(Λ) = β U_f(Λ)`; left multiplication by a unit `b` of `B` carries `I(α)` onto `I(bα)`;
and `I(1) = Λ`. Restricted ideles thus act on full lattices by prescribing all their completions;
this is the input for describing locally free lattices over an order by idele double cosets.
The local lattices `α_v Λ_v` are pointwise translates `α_v • Λ_v` of submodules.

## Main definitions

* `TauCeti.OrderIdeles.FiniteIdeles F Λ`: the finite idele group `J_f(Λ)`.
* `TauCeti.OrderIdeles.unitIdeles F Λ`: the subgroup `U_f(Λ)` of unit ideles.
* `TauCeti.OrderIdeles.principal F Λ hΛ`: the diagonal map `Bˣ →* J_f(Λ)`.
* `TauCeti.OrderIdeles.lattice F Λ α`: the lattice `I(α) = B ∩ ∏_v α_v Λ_v`.

## Main results

* `TauCeti.OrderIdeles.baseChange_lattice`: the completion of `I(α)` at `v` is `α_v Λ_v`.
* `TauCeti.OrderIdeles.lattice_eq_lattice_iff`: `I(α) = I(β)` if and only if `α⁻¹ β ∈ U_f(Λ)`.
* `TauCeti.OrderIdeles.lattice_principal_mul`: `I(bα) = b I(α)` for a unit `b` of `B`.
* `TauCeti.OrderIdeles.lattice_one`: `I(1) = Λ`.
* `TauCeti.OrderIdeles.mul_mem_lattice`: `I(α)` is a right `Λ`-module.
* `TauCeti.OrderIdeles.isLattice_lattice`: when `Λ` is an order, `I(α)` is an `A`-lattice in `B`.

## References

* A. Fröhlich, *Locally free modules over arithmetic orders*, J. Reine Angew. Math. 274/275
  (1975), 112–138, §2, (2.2), and §5.
* J. Voight, *Quaternion Algebras*, Graduate Texts in Mathematics 288, Springer, 2021,
  Chapter 9 (the local–global dictionary for lattices).
-/

public section

open TensorProduct IsDedekindDomain Submodule
open scoped RestrictedProduct Pointwise

namespace TauCeti.OrderIdeles

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
  {B : Type*} [Ring B] [Algebra A B] (Λ : Subalgebra A B)

/-- The **finite idele group** `J_f(Λ)` of `B` relative to `Λ`: the restricted product of the
unit groups `(𝒪_v ⊗[A] B)ˣ` with respect to the unit groups of the completions `Λ_v`. -/
abbrev FiniteIdeles : Type _ :=
  Πʳ v : HeightOneSpectrum A,
    [(v.adicCompletionIntegers F ⊗[A] B)ˣ,
      (Λ.baseChange (v.adicCompletionIntegers F)).toSubmonoid.units]

/-- The subgroup `U_f(Λ)` of **unit ideles**: the finite ideles with every component a unit of
`Λ_v`. -/
def unitIdeles : Subgroup (FiniteIdeles F Λ) where
  carrier := {α | ∀ v, α v ∈ (Λ.baseChange (v.adicCompletionIntegers F)).toSubmonoid.units}
  mul_mem' hα hβ v := mul_mem (hα v) (hβ v)
  one_mem' _ := one_mem _
  inv_mem' hα v := inv_mem (hα v)

variable {F Λ}

@[simp]
theorem mem_unitIdeles {α : FiniteIdeles F Λ} :
    α ∈ unitIdeles F Λ ↔ ∀ v, α v ∈ (Λ.baseChange (v.adicCompletionIntegers F)).toSubmonoid.units :=
  Iff.rfl

variable (F Λ) in
/-- The **lattice of a finite idele**: `I(α) = B ∩ ∏_v α_v Λ_v`, the elements of `B` whose image
in `𝒪_v ⊗[A] B` lies in `α_v Λ_v` for every `v`. -/
noncomputable def lattice (α : FiniteIdeles F Λ) : Submodule A B :=
  glueCompletions F fun v ↦ α v • Subalgebra.toSubmodule (Λ.baseChange (v.adicCompletionIntegers F))

@[simp]
theorem mem_lattice_iff {α : FiniteIdeles F Λ} {x : B} :
    x ∈ lattice F Λ α ↔
      ∀ v : HeightOneSpectrum A, ↑(α v)⁻¹ * ((1 : v.adicCompletionIntegers F) ⊗ₜ[A] x) ∈
        Λ.baseChange (v.adicCompletionIntegers F) := by
  simp only [lattice, mem_glueCompletions]
  exact forall_congr' fun v ↦ Submodule.mem_pointwise_smul_iff_inv_smul_mem (g := α v)

/-- **`I(α)` is a right `Λ`-module.** -/
theorem mul_mem_lattice {α : FiniteIdeles F Λ} {x y : B} (hx : x ∈ lattice F Λ α) (hy : y ∈ Λ) :
    x * y ∈ lattice F Λ α := by
  rw [mem_lattice_iff] at hx ⊢
  intro v
  have := mul_mem (hx v) (Subalgebra.tmul_mem_baseChange hy 1)
  rwa [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this

/-- **The identity idele gives `Λ`.** -/
@[simp]
theorem lattice_one (hA : ¬IsField A) : lattice F Λ 1 = Subalgebra.toSubmodule Λ := by
  conv_rhs => rw [← glueCompletions_baseChange (K := F) hA (Subalgebra.toSubmodule Λ)]
  ext x
  simp [mem_lattice_iff, mem_glueCompletions, ← Subalgebra.toSubmodule_baseChange]

variable [Algebra F B] [IsScalarTower A F B]

variable (F Λ) in
/-- The **principal ideles**: a unit `b` of `B` has components `1 ⊗ₜ b`, which are units of `Λ_v`
for all but finitely many `v` when `Λ` spans `B`. -/
noncomputable def principal (hΛ : span F (Λ : Set B) = ⊤) : Bˣ →* FiniteIdeles F Λ where
  toFun b := .mk (fun v ↦ Units.map (Algebra.TensorProduct.includeRight :
      B →ₐ[A] v.adicCompletionIntegers F ⊗[A] B).toMonoidHom b) <| by
    obtain ⟨a₁, ha₁, h₁⟩ := IsLattice.exists_ne_zero_smul_mem F (Subalgebra.toSubmodule Λ) hΛ
      (b : B)
    obtain ⟨a₂, ha₂, h₂⟩ := IsLattice.exists_ne_zero_smul_mem F (Subalgebra.toSubmodule Λ) hΛ
      (↑b⁻¹ : B)
    -- Off the finitely many primes containing `a₁ a₂`, both `b` and `b⁻¹` are integral.
    have hfin : {v : HeightOneSpectrum A | v.asIdeal ∣ Ideal.span {a₁ * a₂}}.Finite :=
      Ideal.finite_factors (by simpa using mul_ne_zero ha₁ ha₂)
    refine Filter.eventually_cofinite.2 (hfin.subset fun v hv ↦ ?_)
    rw [Set.mem_ofPred_eq, Ideal.dvd_span_singleton]
    by_contra h
    refine hv ⟨(Subalgebra.toSubmodule Λ).one_tmul_mem_baseChange_of_smul_mem
      ((v.isUnit_algebraMap_adicCompletionIntegers_iff (K := F) _).2
        fun h' ↦ h (Ideal.mul_mem_right _ _ h')) h₁,
      (Subalgebra.toSubmodule Λ).one_tmul_mem_baseChange_of_smul_mem
        ((v.isUnit_algebraMap_adicCompletionIntegers_iff (K := F) _).2
          fun h' ↦ h (Ideal.mul_mem_left _ _ h')) h₂⟩
  map_one' := RestrictedProduct.ext _ _ fun _ ↦ Units.ext (by simp)
  map_mul' _ _ := RestrictedProduct.ext _ _ fun _ ↦ Units.ext (by simp)

@[simp]
theorem coe_principal_apply (hΛ : span F (Λ : Set B) = ⊤) (b : Bˣ) (v : HeightOneSpectrum A) :
    ((principal F Λ hΛ b v : (v.adicCompletionIntegers F ⊗[A] B)ˣ) :
      v.adicCompletionIntegers F ⊗[A] B) = 1 ⊗ₜ (b : B) :=
  (rfl)

/-- A single nonzero `a ∈ A` makes `a • α_v⁻¹` integral at every `v`. -/
theorem exists_ne_zero_forall_smul_inv_mem_baseChange (hΛ : span F (Λ : Set B) = ⊤)
    (α : FiniteIdeles F Λ) :
    ∃ a : A, a ≠ 0 ∧
      ∀ v, a • (↑(α v)⁻¹ : v.adicCompletionIntegers F ⊗[A] B) ∈
        Λ.baseChange (v.adicCompletionIntegers F) := by
  classical
  -- Off a finite set `S` of places the components are units of `Λ_v`; take the product of
  -- denominators of `α_v⁻¹` over `S`.
  have hS := Filter.eventually_cofinite.1 α.eventually
  set S := hS.toFinset
  choose c hc0 hc using fun v ↦
    (Subalgebra.toSubmodule Λ).exists_ne_zero_smul_mem_baseChange F hΛ
      (↑(α v)⁻¹ : v.adicCompletionIntegers F ⊗[A] B)
  refine ⟨∏ v ∈ S, c v, Finset.prod_ne_zero_iff.2 fun v _ ↦ hc0 v, fun v ↦ ?_⟩
  by_cases hv : v ∈ S
  · rw [← Finset.mul_prod_erase S c hv, mul_comm, mul_smul]
    exact (Λ.baseChange _).toSubmodule.smul_of_tower_mem _ (hc v)
  · refine (Λ.baseChange _).toSubmodule.smul_of_tower_mem _ ?_
    have : α v ∈ (Λ.baseChange (v.adicCompletionIntegers F)).toSubmonoid.units := by
      simpa [S] using hv
    exact this.2

/-- `I(α)` spans `B` over `F`. -/
theorem span_lattice (hΛ : span F (Λ : Set B) = ⊤) (α : FiniteIdeles F Λ) :
    span F (lattice F Λ α : Set B) = ⊤ := by
  obtain ⟨a, ha, hav⟩ := exists_ne_zero_forall_smul_inv_mem_baseChange hΛ α
  have ha' : algebraMap A F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A F)).2 ha
  refine eq_top_iff.2 (hΛ.ge.trans (span_le.2 fun x hx ↦ ?_))
  -- `a • x ∈ I(α)`, and `x = a⁻¹ • (a • x)`.
  have hmem : a • x ∈ lattice F Λ α := by
    refine mem_lattice_iff.2 fun v ↦ ?_
    have := mul_mem (hav v) (Subalgebra.tmul_mem_baseChange hx 1)
    rwa [smul_mul_assoc, ← mul_smul_comm, ← tmul_smul] at this
  rw [← algebraMap_smul F a x] at hmem
  exact (smul_mem_iff _ ha').1 (subset_span (R := F) hmem)

/-- **The completions of `I(α)`.** The completion of `I(α)` at every `v` is `α_v Λ_v`. -/
theorem baseChange_lattice (hΛ : span F (Λ : Set B) = ⊤) (α : FiniteIdeles F Λ)
    (v : HeightOneSpectrum A) :
    (lattice F Λ α).baseChange (v.adicCompletionIntegers F) =
      α v • Subalgebra.toSubmodule (Λ.baseChange (v.adicCompletionIntegers F)) :=
  baseChange_glueCompletions (span_lattice hΛ α) v

/-- **Unit change.** `I(α) = I(β)` exactly when `α U_f(Λ) = β U_f(Λ)`, that is, when
`α⁻¹ β` is a unit idele. -/
theorem lattice_eq_lattice_iff (hΛ : span F (Λ : Set B) = ⊤) {α β : FiniteIdeles F Λ} :
    lattice F Λ α = lattice F Λ β ↔ α⁻¹ * β ∈ unitIdeles F Λ := by
  simp only [mem_unitIdeles, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
    ← Subalgebra.smul_toSubmodule_eq_smul_toSubmodule_iff]
  refine ⟨fun h v ↦ ?_, fun h ↦ ?_⟩
  · rw [← baseChange_lattice hΛ, ← baseChange_lattice hΛ, h]
  · simp only [lattice, h]

/-- **Principal change.** Left multiplication by a unit `b` of `B` carries `I(α)` onto
`I(bα)`. -/
theorem lattice_principal_mul (hΛ : span F (Λ : Set B) = ⊤) (b : Bˣ) (α : FiniteIdeles F Λ) :
    lattice F Λ (principal F Λ hΛ b * α) =
      b • lattice F Λ α := by
  ext x
  refine Iff.trans ?_ (Submodule.mem_pointwise_smul_iff_inv_smul_mem
    (N := lattice F Λ α) (g := b) (x := x)).symm
  rw [mem_lattice_iff, mem_lattice_iff]
  simp only [Units.smul_def, smul_eq_mul]
  refine forall_congr' fun v ↦ ?_
  have hb : (↑(principal F Λ hΛ b v)⁻¹ : v.adicCompletionIntegers F ⊗[A] B) = 1 ⊗ₜ ↑b⁻¹ := by
    rw [← RestrictedProduct.inv_apply, ← map_inv, coe_principal_apply]
  rw [RestrictedProduct.mul_apply, mul_inv_rev, Units.val_mul, mul_assoc, hb,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/-- **`I(α)` is a full lattice.** When `Λ` is an `A`-order in `B` and `A` is not a field, `I(α)` is
an `A`-lattice in `B`: finitely generated and spanning `B` over `F`. -/
theorem isLattice_lattice (hA : ¬IsField A) (hΛ : IntegralOrder.IsOrder F Λ)
    (α : FiniteIdeles F Λ) : (lattice F Λ α).IsLattice F := by
  refine ⟨?_, span_lattice hΛ.span_eq_top α⟩
  -- Some nonzero `a ∈ A` makes every `a • α_v` integral, so that `a • I(α) ⊆ I(1) = Λ`.
  obtain ⟨a, ha, hav⟩ := exists_ne_zero_forall_smul_inv_mem_baseChange hΛ.span_eq_top α⁻¹
  have ha' : algebraMap A F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A F)).2 ha
  have hinj : Function.Injective (LinearMap.lsmul A B a) := by
    intro x y hxy
    rw [LinearMap.lsmul_apply, LinearMap.lsmul_apply, ← algebraMap_smul F a x,
      ← algebraMap_smul F a y] at hxy
    exact smul_right_injective B ha' hxy
  refine fg_of_fg_map_injective _ hinj
    (FG.of_le (IntegralOrder.isOrder_iff_isLattice.1 hΛ).fg ?_)
  rw [← lattice_one (F := F) hA]
  rintro _ ⟨x, hx, rfl⟩
  refine mem_lattice_iff.2 fun v ↦ ?_
  have := mul_mem (hav v) (mem_lattice_iff.1 hx v)
  simpa [smul_mul_assoc, tmul_smul] using this

end TauCeti.OrderIdeles
