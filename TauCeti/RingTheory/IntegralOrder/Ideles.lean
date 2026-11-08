/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Topology.Algebra.RestrictedProduct.Basic
public import TauCeti.RingTheory.DedekindDomain.AdicValuation.Gluing
public import TauCeti.RingTheory.IntegralOrder.Basic
import Mathlib.RingTheory.DedekindDomain.Factorization
import TauCeti.Algebra.Module.Lattice

/-!
# Finite ideles of an order and the lattices they define

Let `A` be a Dedekind domain with fraction field `F`, let `B` be an `F`-algebra (not necessarily
commutative), and let `Λ` be an `A`-subalgebra of `B` spanning `B` over `F`, for instance an
`A`-order in `B`. For a height-one prime `v` of `A` write `𝒪_v` for the ring of integers of the
completion `F_v`. We take `B_v = 𝒪_v ⊗[A] B` as the completion of `B` at `v`: since every nonzero
element of `A` acts invertibly on `B`, it is canonically `F_v ⊗[F] B`. The completion of `Λ` is
its image `Λ_v = 𝒪_v Λ` in `B_v`, an `𝒪_v`-subalgebra (`TauCeti.OrderIdeles.localOrder`).

The finite idele group `J_f(Λ)` is the restricted product of the unit groups `B_vˣ` with respect
to the unit groups `Λ_vˣ`, and `U_f(Λ) ⊆ J_f(Λ)` is the subgroup of ideles with every component
in `Λ_vˣ`. Units of `B` map diagonally to `J_f(Λ)`.

To a finite idele `α` we attach the right `Λ`-lattice `I(α) = B ∩ ∏_v α_v Λ_v`
(`TauCeti.OrderIdeles.lattice`), glued from the local lattices `α_v Λ_v` with
`TauCeti.glueCompletions`. Its completion at every `v` is exactly `α_v Λ_v`; `I(α) = I(β)` exactly
when `α U_f(Λ) = β U_f(Λ)`; left multiplication by a unit `b` of `B` carries `I(α)` onto `I(bα)`;
and `I(1) = Λ`. Restricted ideles thus act on full lattices by prescribing all their completions;
this is the input for describing locally free lattices over an order by idele double cosets.

## Main definitions

* `TauCeti.OrderIdeles.localOrder F Λ v`: the completion `Λ_v` of `Λ` at `v`.
* `TauCeti.OrderIdeles.FiniteIdeles F Λ`: the finite idele group `J_f(Λ)`.
* `TauCeti.OrderIdeles.unitIdeles F Λ`: the subgroup `U_f(Λ)` of unit ideles.
* `TauCeti.OrderIdeles.principal F Λ hΛ`: the diagonal map `Bˣ →* J_f(Λ)`.
* `TauCeti.OrderIdeles.localLattice F Λ s`: the translate `s Λ_v` of `Λ_v` by a unit `s`.
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
open scoped RestrictedProduct

namespace TauCeti.OrderIdeles

variable {A : Type*} [CommRing A] [IsDedekindDomain A]
  (F : Type*) [Field F] [Algebra A F] [IsFractionRing A F]
  {B : Type*} [Ring B] [Algebra A B] (Λ : Subalgebra A B)

/-- The completion `Λ_v = 𝒪_v Λ` of `Λ` at `v`: the `𝒪_v`-subalgebra of `𝒪_v ⊗[A] B` spanned by
the image of `Λ`. -/
noncomputable def localOrder (v : HeightOneSpectrum A) :
    Subalgebra (v.adicCompletionIntegers F) (v.adicCompletionIntegers F ⊗[A] B) :=
  ((Subalgebra.toSubmodule Λ).baseChange (v.adicCompletionIntegers F)).toSubalgebra
    (by rw [Algebra.TensorProduct.one_def]; exact tmul_mem_baseChange_of_mem _ Λ.one_mem)
    fun {x y} hx hy ↦ by
      rw [baseChange_eq_span] at hx hy ⊢
      have hxy := mul_mem_mul hx hy
      rw [span_mul_span] at hxy
      refine span_mono ?_ hxy
      rintro _ ⟨_, ⟨a, ha, rfl⟩, _, ⟨b, hb, rfl⟩, rfl⟩
      exact ⟨a * b, Λ.mul_mem ha hb, by simp⟩

variable {F Λ}

@[simp]
theorem toSubmodule_localOrder (v : HeightOneSpectrum A) :
    Subalgebra.toSubmodule (localOrder F Λ v) =
      (Subalgebra.toSubmodule Λ).baseChange (v.adicCompletionIntegers F) :=
  Submodule.toSubalgebra_toSubmodule _ _ _

theorem mem_localOrder_iff {v : HeightOneSpectrum A} {z : v.adicCompletionIntegers F ⊗[A] B} :
    z ∈ localOrder F Λ v ↔
      z ∈ (Subalgebra.toSubmodule Λ).baseChange (v.adicCompletionIntegers F) := by
  rw [← toSubmodule_localOrder, Subalgebra.mem_toSubmodule]

theorem tmul_mem_localOrder (v : HeightOneSpectrum A) (o : v.adicCompletionIntegers F)
    {x : B} (hx : x ∈ Λ) : o ⊗ₜ x ∈ localOrder F Λ v :=
  mem_localOrder_iff.2 (tmul_mem_baseChange_of_mem o hx)

/-- The `A`-module structure on `𝒪_v ⊗[A] B` preserves `Λ_v`. -/
theorem smul_mem_localOrder {v : HeightOneSpectrum A} (a : A)
    {z : v.adicCompletionIntegers F ⊗[A] B} (hz : z ∈ localOrder F Λ v) :
    a • z ∈ localOrder F Λ v := by
  rw [← algebraMap_smul (v.adicCompletionIntegers F)]
  exact Subalgebra.smul_mem _ hz _

/-- If `a • x ∈ Λ` for an element `a` of `A` outside `v`, then `1 ⊗ₜ x ∈ Λ_v`, since `a` is a
unit of `𝒪_v`. -/
theorem one_tmul_mem_localOrder_of_smul_mem {v : HeightOneSpectrum A} {a : A}
    (ha : a ∉ v.asIdeal) {x : B} (hx : a • x ∈ Λ) :
    (1 : v.adicCompletionIntegers F) ⊗ₜ x ∈ localOrder F Λ v := by
  obtain ⟨u, hu⟩ := (v.isUnit_algebraMap_adicCompletionIntegers_iff (K := F) a).2 ha
  have h := Subalgebra.smul_mem _ (tmul_mem_localOrder v 1 hx) (↑u⁻¹ : v.adicCompletionIntegers F)
  rwa [← smul_tmul, ← Algebra.algebraMap_eq_smul_one, ← hu, smul_tmul', smul_eq_mul,
    Units.inv_mul] at h

variable (F Λ)

/-- The **finite idele group** `J_f(Λ)` of `B` relative to `Λ`: the restricted product of the
unit groups `(𝒪_v ⊗[A] B)ˣ` with respect to the unit groups of the completions `Λ_v`. -/
abbrev FiniteIdeles : Type _ :=
  Πʳ v : HeightOneSpectrum A,
    [(v.adicCompletionIntegers F ⊗[A] B)ˣ, (localOrder F Λ v).toSubmonoid.units]

/-- The subgroup `U_f(Λ)` of **unit ideles**: the finite ideles with every component a unit of
`Λ_v`. -/
def unitIdeles : Subgroup (FiniteIdeles F Λ) where
  carrier := {α | ∀ v, α v ∈ (localOrder F Λ v).toSubmonoid.units}
  mul_mem' hα hβ v := mul_mem (hα v) (hβ v)
  one_mem' _ := one_mem _
  inv_mem' hα v := inv_mem (hα v)

variable {F Λ}

@[simp]
theorem mem_unitIdeles {α : FiniteIdeles F Λ} :
    α ∈ unitIdeles F Λ ↔ ∀ v, α v ∈ (localOrder F Λ v).toSubmonoid.units :=
  Iff.rfl

variable (F Λ) in
/-- The translate `s Λ_v` of the completion `Λ_v` by a unit `s` of `𝒪_v ⊗[A] B`, as an
`𝒪_v`-submodule. -/
noncomputable def localLattice {v : HeightOneSpectrum A}
    (s : (v.adicCompletionIntegers F ⊗[A] B)ˣ) :
    Submodule (v.adicCompletionIntegers F) (v.adicCompletionIntegers F ⊗[A] B) :=
  (Subalgebra.toSubmodule (localOrder F Λ v)).map
    (DistribMulAction.toLinearEquiv (v.adicCompletionIntegers F)
      (v.adicCompletionIntegers F ⊗[A] B) s : _ →ₗ[v.adicCompletionIntegers F] _)

theorem mem_localLattice_iff {v : HeightOneSpectrum A} {s : (v.adicCompletionIntegers F ⊗[A] B)ˣ}
    {z : v.adicCompletionIntegers F ⊗[A] B} :
    z ∈ localLattice F Λ s ↔ ↑s⁻¹ * z ∈ localOrder F Λ v := by
  rw [localLattice, mem_map_equiv, Subalgebra.mem_toSubmodule,
    DistribMulAction.toLinearEquiv_symm_apply, Units.smul_def, smul_eq_mul]

variable (F Λ) in
/-- The **lattice of a finite idele**: `I(α) = B ∩ ∏_v α_v Λ_v`, the elements of `B` whose image
in `𝒪_v ⊗[A] B` lies in `α_v Λ_v` for every `v`. -/
noncomputable def lattice (α : FiniteIdeles F Λ) : Submodule A B :=
  glueCompletions F fun v ↦ localLattice F Λ (α v)

theorem mem_lattice_iff {α : FiniteIdeles F Λ} {x : B} :
    x ∈ lattice F Λ α ↔
      ∀ v : HeightOneSpectrum A, ↑(α v)⁻¹ * ((1 : v.adicCompletionIntegers F) ⊗ₜ[A] x) ∈
        localOrder F Λ v := by
  simp only [lattice, mem_glueCompletions, mem_localLattice_iff]

/-- **`I(α)` is a right `Λ`-module.** -/
theorem mul_mem_lattice {α : FiniteIdeles F Λ} {x y : B} (hx : x ∈ lattice F Λ α) (hy : y ∈ Λ) :
    x * y ∈ lattice F Λ α := by
  rw [mem_lattice_iff] at hx ⊢
  intro v
  have := mul_mem (hx v) (tmul_mem_localOrder v 1 hy)
  rwa [mul_assoc, Algebra.TensorProduct.tmul_mul_tmul, mul_one] at this

/-- Two translates `s Λ_v` and `t Λ_v` agree exactly when `s⁻¹ t` is a unit of `Λ_v`. -/
theorem localLattice_eq_localLattice_iff {v : HeightOneSpectrum A}
    {s t : (v.adicCompletionIntegers F ⊗[A] B)ˣ} :
    localLattice F Λ s = localLattice F Λ t ↔ s⁻¹ * t ∈ (localOrder F Λ v).toSubmonoid.units := by
  -- If `s Λ_v ≤ t Λ_v`, then `s ∈ t Λ_v`, that is `t⁻¹ s ∈ Λ_v`.
  have key {s t : (v.adicCompletionIntegers F ⊗[A] B)ˣ}
      (h : localLattice F Λ s ≤ localLattice F Λ t) :
      (↑(t⁻¹ * s) : v.adicCompletionIntegers F ⊗[A] B) ∈ localOrder F Λ v := by
    have hs : (s : v.adicCompletionIntegers F ⊗[A] B) ∈ localLattice F Λ s := by
      simp [mem_localLattice_iff]
    simpa [mem_localLattice_iff] using h hs
  refine ⟨fun h ↦ ⟨key h.ge, by simpa using key h.le⟩, fun h ↦ ?_⟩
  -- If `u = s⁻¹ t` is a unit of `Λ_v`, then `t Λ_v = s u Λ_v = s Λ_v`.
  obtain ⟨h₁, h₂⟩ := (Submonoid.mem_units_iff _ _).1 h
  rw [Subsemiring.mem_toSubmonoid, Subalgebra.mem_toSubsemiring] at h₁ h₂
  ext z
  simp only [mem_localLattice_iff]
  constructor
  · intro hz
    have := mul_mem h₂ hz
    rwa [← mul_assoc, ← Units.val_mul, mul_inv_rev, inv_inv, mul_inv_cancel_right] at this
  · intro hz
    have := mul_mem h₁ hz
    rwa [← mul_assoc, ← Units.val_mul, mul_assoc, mul_inv_cancel, mul_one] at this

/-- **The identity idele gives `Λ`.** -/
theorem lattice_one (hA : ¬IsField A) : lattice F Λ 1 = Subalgebra.toSubmodule Λ := by
  conv_rhs => rw [← glueCompletions_baseChange (K := F) hA (Subalgebra.toSubmodule Λ)]
  ext x
  simp [mem_lattice_iff, mem_glueCompletions, mem_localOrder_iff]

variable [Algebra F B] [IsScalarTower A F B]

variable (Λ) in
/-- Every element of `𝒪_v ⊗[A] B` has a nonzero `A`-multiple in `Λ_v` when `Λ` spans `B`. -/
theorem exists_ne_zero_smul_mem_localOrder (hΛ : span F (Λ : Set B) = ⊤)
    {v : HeightOneSpectrum A} (z : v.adicCompletionIntegers F ⊗[A] B) :
    ∃ a : A, a ≠ 0 ∧ a • z ∈ localOrder F Λ v := by
  induction z using TensorProduct.inductionOn with
  | tmul o x =>
    obtain ⟨a, ha, hax⟩ := IsLattice.exists_ne_zero_smul_mem F (Subalgebra.toSubmodule Λ) hΛ x
    exact ⟨a, ha, by rw [← tmul_smul]; exact tmul_mem_localOrder v o hax⟩
  | add z₁ z₂ h₁ h₂ =>
    obtain ⟨a₁, ha₁, h₁⟩ := h₁
    obtain ⟨a₂, ha₂, h₂⟩ := h₂
    refine ⟨a₂ * a₁, mul_ne_zero ha₂ ha₁, ?_⟩
    rw [smul_add, mul_smul, mul_comm, mul_smul]
    exact add_mem (smul_mem_localOrder a₂ h₁) (smul_mem_localOrder a₁ h₂)

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
    refine hv ⟨one_tmul_mem_localOrder_of_smul_mem (fun h' ↦ h (Ideal.mul_mem_right _ _ h')) h₁,
      one_tmul_mem_localOrder_of_smul_mem (fun h' ↦ h (Ideal.mul_mem_left _ _ h')) h₂⟩
  map_one' := RestrictedProduct.ext _ _ fun _ ↦ Units.ext (by simp)
  map_mul' _ _ := RestrictedProduct.ext _ _ fun _ ↦ Units.ext (by simp)

@[simp]
theorem coe_principal_apply (hΛ : span F (Λ : Set B) = ⊤) (b : Bˣ) (v : HeightOneSpectrum A) :
    ((principal F Λ hΛ b v : (v.adicCompletionIntegers F ⊗[A] B)ˣ) :
      v.adicCompletionIntegers F ⊗[A] B) = 1 ⊗ₜ (b : B) :=
  (rfl)

/-- A single nonzero `a ∈ A` makes `a • α_v⁻¹` integral at every `v`. -/
theorem exists_ne_zero_forall_smul_inv_mem_localOrder (hΛ : span F (Λ : Set B) = ⊤)
    (α : FiniteIdeles F Λ) :
    ∃ a : A, a ≠ 0 ∧
      ∀ v, a • (↑(α v)⁻¹ : v.adicCompletionIntegers F ⊗[A] B) ∈ localOrder F Λ v := by
  classical
  -- Off a finite set `S` of places the components are units of `Λ_v`; take the product of
  -- denominators of `α_v⁻¹` over `S`.
  have hS := Filter.eventually_cofinite.1 α.eventually
  set S := hS.toFinset
  choose c hc0 hc using fun v ↦ exists_ne_zero_smul_mem_localOrder Λ hΛ (↑(α v)⁻¹ :
    v.adicCompletionIntegers F ⊗[A] B)
  refine ⟨∏ v ∈ S, c v, Finset.prod_ne_zero_iff.2 fun v _ ↦ hc0 v, fun v ↦ ?_⟩
  by_cases hv : v ∈ S
  · rw [← Finset.mul_prod_erase S c hv, mul_comm, mul_smul]
    exact smul_mem_localOrder _ (hc v)
  · refine smul_mem_localOrder _ ?_
    have : α v ∈ (localOrder F Λ v).toSubmonoid.units := by simpa [S] using hv
    exact this.2

/-- `I(α)` spans `B` over `F`. -/
theorem span_lattice (hΛ : span F (Λ : Set B) = ⊤) (α : FiniteIdeles F Λ) :
    span F (lattice F Λ α : Set B) = ⊤ := by
  obtain ⟨a, ha, hav⟩ := exists_ne_zero_forall_smul_inv_mem_localOrder hΛ α
  have ha' : algebraMap A F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A F)).2 ha
  refine eq_top_iff.2 (hΛ.ge.trans (span_le.2 fun x hx ↦ ?_))
  -- `a • x ∈ I(α)`, and `x = a⁻¹ • (a • x)`.
  have hmem : a • x ∈ lattice F Λ α := by
    refine mem_lattice_iff.2 fun v ↦ ?_
    have := mul_mem (hav v) (tmul_mem_localOrder v 1 hx)
    rwa [smul_mul_assoc, ← mul_smul_comm, ← tmul_smul] at this
  have := smul_mem _ (algebraMap A F a)⁻¹ (subset_span (R := F) hmem)
  rwa [← algebraMap_smul F a x, smul_smul, inv_mul_cancel₀ ha', one_smul] at this

/-- **The completions of `I(α)`.** The completion of `I(α)` at every `v` is `α_v Λ_v`. -/
theorem baseChange_lattice (hΛ : span F (Λ : Set B) = ⊤) (α : FiniteIdeles F Λ)
    (v : HeightOneSpectrum A) :
    (lattice F Λ α).baseChange (v.adicCompletionIntegers F) = localLattice F Λ (α v) :=
  baseChange_glueCompletions (span_lattice hΛ α) v

/-- **Unit change.** `I(α) = I(β)` exactly when `α U_f(Λ) = β U_f(Λ)`, that is, when
`α⁻¹ β` is a unit idele. -/
theorem lattice_eq_lattice_iff (hΛ : span F (Λ : Set B) = ⊤) {α β : FiniteIdeles F Λ} :
    lattice F Λ α = lattice F Λ β ↔ α⁻¹ * β ∈ unitIdeles F Λ := by
  simp only [mem_unitIdeles, RestrictedProduct.mul_apply, RestrictedProduct.inv_apply,
    ← localLattice_eq_localLattice_iff]
  refine ⟨fun h v ↦ ?_, fun h ↦ ?_⟩
  · rw [← baseChange_lattice hΛ, ← baseChange_lattice hΛ, h]
  · simp only [lattice, h]

/-- **Principal change.** Left multiplication by a unit `b` of `B` carries `I(α)` onto
`I(bα)`. -/
theorem lattice_principal_mul (hΛ : span F (Λ : Set B) = ⊤) (b : Bˣ) (α : FiniteIdeles F Λ) :
    lattice F Λ (principal F Λ hΛ b * α) =
      (lattice F Λ α).map (DistribMulAction.toLinearEquiv A B b : B →ₗ[A] B) := by
  ext x
  rw [mem_map_equiv, mem_lattice_iff, mem_lattice_iff]
  refine forall_congr' fun v ↦ ?_
  have hb : (↑(principal F Λ hΛ b v)⁻¹ : v.adicCompletionIntegers F ⊗[A] B) = 1 ⊗ₜ ↑b⁻¹ := by
    rw [← RestrictedProduct.inv_apply, ← map_inv, coe_principal_apply]
  rw [RestrictedProduct.mul_apply, mul_inv_rev, Units.val_mul, mul_assoc, hb,
    Algebra.TensorProduct.tmul_mul_tmul, one_mul, DistribMulAction.toLinearEquiv_symm_apply,
    Units.smul_def, smul_eq_mul]

/-- **`I(α)` is a full lattice.** When `Λ` is an `A`-order in `B` and `A` is not a field, `I(α)` is
an `A`-lattice in `B`: finitely generated and spanning `B` over `F`. -/
theorem isLattice_lattice (hA : ¬IsField A) (hΛ : IntegralOrder.IsOrder F Λ)
    (α : FiniteIdeles F Λ) : (lattice F Λ α).IsLattice F := by
  refine ⟨?_, span_lattice hΛ.span_eq_top α⟩
  -- Some nonzero `a ∈ A` makes every `a • α_v` integral, so that `a • I(α) ⊆ I(1) = Λ`.
  obtain ⟨a, ha, hav⟩ := exists_ne_zero_forall_smul_inv_mem_localOrder hΛ.span_eq_top α⁻¹
  have ha' : algebraMap A F a ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective A F)).2 ha
  have hinj : Function.Injective (LinearMap.lsmul A B a) := fun x y hxy ↦ by
    rw [LinearMap.lsmul_apply, LinearMap.lsmul_apply, ← algebraMap_smul F a x,
      ← algebraMap_smul F a y] at hxy
    have := congr_arg ((algebraMap A F a)⁻¹ • ·) hxy
    rwa [smul_smul, smul_smul, inv_mul_cancel₀ ha', one_smul, one_smul] at this
  refine fg_of_fg_map_injective _ hinj
    (FG.of_le (IntegralOrder.isOrder_iff_isLattice.1 hΛ).fg ?_)
  rw [← lattice_one (F := F) hA]
  rintro _ ⟨x, hx, rfl⟩
  refine mem_lattice_iff.2 fun v ↦ ?_
  have := mul_mem (hav v) (mem_lattice_iff.1 hx v)
  simpa [smul_mul_assoc, tmul_smul] using this

end TauCeti.OrderIdeles
