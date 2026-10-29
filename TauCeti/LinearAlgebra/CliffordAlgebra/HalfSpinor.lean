/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.CliffordAlgebra.Even
public import Mathlib.LinearAlgebra.Complex.FiniteDimensional
public import Mathlib.LinearAlgebra.Determinant
public import Mathlib.LinearAlgebra.Eigenspace.Basic
public import Mathlib.LinearAlgebra.Trace
public import TauCeti.LinearAlgebra.CliffordAlgebra.Chirality
public import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian
public import TauCeti.LinearAlgebra.CliffordAlgebra.Reversal.Basic
-- Private: the orthogonal vector, even relation, conjugation and adjugate facts are proof-only.
import TauCeti.Analysis.InnerProductSpace.Projection.Basic
import TauCeti.LinearAlgebra.CliffordAlgebra.Even.Conjugation
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.End.Adjugate

/-!
# Clifford multiplication and the even action on the half-spinors of an oriented four-space

Let `V` be an oriented real inner product space of dimension four, `Q v = -‖v‖²`, and let `W` be
a finite-dimensional complex vector space with a real algebra map
`ρ : CliffordAlgebra Q → End_ℂ W`; write `c(v) = ρ (ι Q v)`. The chirality element `Γ`
(`CliffordAlgebra.chirality`) splits `W` into its `±1` eigenspaces `W⁺` and `W⁻`.

This file proves the facts about `Γ` and the generators that the linearized Seiberg–Witten
equations use; they hold for every such Clifford module. Each generator `c(v)` exchanges the two
eigenspaces, and is injective for `v ≠ 0` since `c(v)² = -‖v‖²`, so the eigenspaces have the same
dimension. The main result: for a nonzero
`ψ` in one eigenspace, Clifford multiplication `v ↦ c(v) ψ` is a real-linear isomorphism of `V`
onto the other eigenspace when the eigenspaces have complex dimension two. It is injective
because `c(v) ψ = 0` forces `‖v‖² ψ = 0`, and both sides have real dimension four.

When `W` is moreover a Hermitian Clifford module, that is, a complex inner product space on which
the generators act skew-adjointly, `c(v)* = -c(v)`, the chirality `Γ` acts self-adjointly. On a
complex inner product space, for a nonzero `ψ` in a two-dimensional eigenspace, a spinor `χ` of
the opposite eigenspace with `Re ⟪c(v) ψ, χ⟫ = 0` for every `v` vanishes. This is the pointwise
step of the unique-continuation argument for the cokernel of the linearized Seiberg–Witten map:
the variations `a ↦ c(a) ψ` of the Dirac term force such a cokernel element to vanish at every
point where `ψ ≠ 0`.

The eigenspaces are stated for an arbitrary eigenvalue `ε`: `c(v)` maps the `ε`-eigenspace to
the `-ε`-eigenspace, and the case `ε = 1` is `W⁺ → W⁻`.

Since `Γ` commutes with every even Clifford element, the even subalgebra acts on each eigenspace
`W^ε`. When `W^ε` has complex dimension two, Clifford conjugation `star` acts on it as the
adjugate: for an even element `x`, `ρ(x*) = tr(ρ x) - ρ x` on `W^ε`. This holds on the generators
`c(u) c(v)`, whose trace on `W^ε` is `-2 ⟪u, v⟫`, and propagates because both sides reverse
products. Consequently `ρ(x* x) = det(ρ x)` on `W^ε`.

## Main definitions

* `CliffordAlgebra.cliffordMulEquiv`: for a nonzero `ψ` in a two-dimensional eigenspace of
  `Γ`, the real-linear isomorphism `v ↦ c(v) ψ` from `V` onto the opposite eigenspace.
* `CliffordAlgebra.evenHalfSpinAction o ρ ε`: the even Clifford subalgebra acting on the
  `ε`-eigenspace of `Γ`.

## Main results

* `CliffordAlgebra.isSelfAdjoint_map_chirality`: `Γ* = Γ`.
* `CliffordAlgebra.trace_evenHalfSpinAction_ι_bilin`: `tr (c(u) c(v)) = -⟪u, v⟫ dim W^ε`.
* `CliffordAlgebra.evenHalfSpinAction_reverseEven`: in complex dimension two, Clifford
  conjugation (on the even subalgebra, `CliffordAlgebra.reverseEven`) acts on `W^ε` as the
  adjugate, and `CliffordAlgebra.evenHalfSpinAction_reverseEven_mul_self`: `x* x` acts by
  `det (ρ x)`; `CliffordAlgebra.map_star_apply_of_mem_even` and
  `CliffordAlgebra.map_star_mul_self_apply_of_mem_even` state both on vectors.
* `CliffordAlgebra.map_ι_apply_mem_eigenspace_chirality_neg`: `c(v)` maps the `ε`-eigenspace of
  `Γ` into the `-ε`-eigenspace.
* `CliffordAlgebra.finrank_eigenspace_chirality_neg`: the two eigenspaces have the same
  dimension.
* `CliffordAlgebra.eq_zero_of_forall_re_inner_map_ι_apply_eq_zero`: if
  `Re ⟪c(v) ψ, χ⟫ = 0` for all `v`, with `ψ ≠ 0` in a two-dimensional `ε`-eigenspace and `χ` in
  the opposite eigenspace, then `χ = 0`.

## References

* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1 and §5.
* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5.
-/

public section

noncomputable section

namespace CliffordAlgebra

open Module Module.End
open scoped InnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

/-- The chirality element acts self-adjointly on a Hermitian Clifford module: `Γ* = Γ`. -/
theorem isSelfAdjoint_map_chirality {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W]
    [FiniteDimensional ℂ W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) :
    IsSelfAdjoint (ρ (chirality Q o)) := by
  rw [LinearMap.isSelfAdjoint_iff', adjoint_map_eq_map_star hρ, star_def, involute_chirality,
    reverse_chirality]

section EvenAction

open scoped RealInnerProductSpace

variable {W : Type*} [AddCommGroup W] [Module ℂ W] (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
  (ε : ℂ)

/-- Even Clifford elements preserve every eigenspace of `Γ`. -/
theorem mapsTo_eigenspace_chirality_of_mem_even {x : CliffordAlgebra Q} (hx : x ∈ even Q) :
    Set.MapsTo (ρ x) (eigenspace (ρ (chirality Q o)) ε) (eigenspace (ρ (chirality Q o)) ε) :=
  fun _ hψ ↦ mapsTo_genEigenspace_of_comm ((commute_chirality_of_mem_even o hx).map ρ) ε 1 hψ

/-- **The even Clifford subalgebra acting on an eigenspace of `Γ`**: an even element `x` acts
on the `ε`-eigenspace `W^ε` by the restriction of `ρ x`. For `ε = ±1` this is the action on the
half-spinors `W^±`. -/
def evenHalfSpinAction : even Q →ₐ[ℝ] Module.End ℂ (eigenspace (ρ (chirality Q o)) ε) where
  toFun x := (ρ x).restrict fun _ hψ ↦ mapsTo_eigenspace_chirality_of_mem_even o ρ ε x.2 hψ
  map_one' := by ext; simp
  map_mul' x y := by ext; simp
  map_zero' := by ext; simp
  map_add' x y := by ext; simp
  commutes' r := by ext; simp [Algebra.algebraMap_eq_smul_one]

/-- `evenHalfSpinAction` is the restriction of the Clifford action. -/
@[simp]
theorem coe_evenHalfSpinAction_apply (x : even Q) (ψ : eigenspace (ρ (chirality Q o)) ε) :
    (evenHalfSpinAction o ρ ε x ψ : W) = ρ x ψ :=
  (rfl)

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

omit hQ in
/-- Real scalars pull out of the trace of the even action. -/
private theorem trace_evenHalfSpinAction_smul (r : ℝ) (x : even Q) :
    LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε (r • x)) =
      r * LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε x) := by
  simp [← Complex.coe_smul]

/-- The trace of `c(u) c(v)` on an eigenspace of `Γ` is symmetric in `u` and `v`: writing
`Q e c(u) c(v) = (c(u) c(e)) (c(e) c(v))` for a vector `e` orthogonal to `u` and `v`, cyclicity of
the trace exchanges the two factors, and `e` anticommutes past `u` and `v`. -/
private theorem trace_evenHalfSpinAction_ι_bilin_comm (u v : V) :
    LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε ((even.ι Q).bilin u v)) =
      LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε ((even.ι Q).bilin v u)) := by
  -- In dimension four, `u` and `v` have a common nonzero orthogonal vector `e`.
  classical
  obtain ⟨e, he₀, he⟩ := TauCeti.exists_ne_zero_forall_inner_eq_zero_of_card_lt_finrank
    (𝕜 := ℝ) {u, v} (Finset.card_le_two.trans_lt (by rw [(Fact.out : finrank ℝ V = 4)]; norm_num))
  have hue : ⟪u, e⟫ = 0 := he u (by simp)
  have hve : ⟪v, e⟫ = 0 := he v (by simp)
  have hQe : Q e ≠ 0 := by simpa [hQ] using he₀
  have hswap : ∀ a, ⟪a, e⟫ = 0 → (even.ι Q).bilin e a = -(even.ι Q).bilin a e := fun a ha ↦
    Subtype.ext (ι_mul_ι_comm_of_isOrtho
      ((QuadraticMap.isOrtho_iff_inner_eq_zero hQ).2 (by rwa [real_inner_comm])))
  -- `(c(u) c(e)) (c(e) c(v)) = Q e c(u) c(v)` and `(c(e) c(v)) (c(u) c(e)) = Q e c(v) c(u)`.
  have h₁ := (even.ι Q).contract_mid u e v
  have h₂ := (even.ι Q).contract_mid v e u
  rw [← neg_neg ((even.ι Q).bilin v e), ← hswap v hve, ← neg_neg ((even.ι Q).bilin e u),
    hswap u hue, neg_neg, neg_mul_neg] at h₂
  have h := LinearMap.trace_mul_comm ℂ (evenHalfSpinAction o ρ ε ((even.ι Q).bilin u e))
    (evenHalfSpinAction o ρ ε ((even.ι Q).bilin e v))
  rw [← map_mul, ← map_mul, h₁, h₂, trace_evenHalfSpinAction_smul,
    trace_evenHalfSpinAction_smul] at h
  exact mul_left_cancel₀ (by exact_mod_cast hQe) h

/-- **The trace of `c(u) c(v)` on an eigenspace of `Γ`** is `-⟪u, v⟫` times its dimension. -/
theorem trace_evenHalfSpinAction_ι_bilin
    [FiniteDimensional ℂ (eigenspace (ρ (chirality Q o)) ε)] (u v : V) :
    LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε ((even.ι Q).bilin u v)) =
      -⟪u, v⟫ * finrank ℂ (eigenspace (ρ (chirality Q o)) ε) := by
  -- By symmetry, twice the trace is the trace of `c(u) c(v) + c(v) c(u) = -2 ⟪u, v⟫`.
  have h := congrArg (fun x ↦ LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε x))
    (even_ι_bilin_add_swap_eq_neg_two_inner hQ u v)
  rw [map_add, map_add, ← trace_evenHalfSpinAction_ι_bilin_comm o ρ ε hQ u v, AlgHom.commutes,
    Algebra.algebraMap_eq_smul_one, ← Complex.coe_smul, map_smul, LinearMap.trace_one,
    smul_eq_mul] at h
  push_cast at h
  linear_combination h / 2

/-- In complex dimension two, `c(v) c(u)` acts on an eigenspace of `Γ` as the adjugate
`tr T - T` of the action `T` of `c(u) c(v)`. -/
private theorem evenHalfSpinAction_ι_bilin_swap
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) (u v : V) :
    evenHalfSpinAction o ρ ε ((even.ι Q).bilin v u) =
      LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε ((even.ι Q).bilin u v)) • 1 -
        evenHalfSpinAction o ρ ε ((even.ι Q).bilin u v) := by
  have : FiniteDimensional ℂ (eigenspace (ρ (chirality Q o)) ε) :=
    Module.finite_of_finrank_eq_succ h₂
  rw [trace_evenHalfSpinAction_ι_bilin o ρ ε hQ, h₂, eq_sub_iff_add_eq', ← map_add,
    even_ι_bilin_add_swap_eq_neg_two_inner hQ, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
    ← Complex.coe_smul]
  push_cast
  ring_nf

/-- **Clifford conjugation acts as the adjugate** on an eigenspace `W^ε` of `Γ` of complex
dimension two: for an even element `x`, `ρ(x*) = tr (ρ x) - ρ x` on `W^ε`, where on the even
subalgebra Clifford conjugation is the reversal `CliffordAlgebra.reverseEven`. Both sides reverse
products, and they agree on the generators. -/
theorem evenHalfSpinAction_reverseEven
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) (x : even Q) :
    evenHalfSpinAction o ρ ε (reverseEven Q x) =
      LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε x) • 1 - evenHalfSpinAction o ρ ε x := by
  have : FiniteDimensional ℂ (eigenspace (ρ (chirality Q o)) ε) :=
    Module.finite_of_finrank_eq_succ h₂
  rcases x with ⟨x, hx⟩
  induction x, hx using even_induction with
  | algebraMap r =>
    -- Dependent even induction exposes the algebra element and its membership proof separately.
    change evenHalfSpinAction o ρ ε (reverseEven Q (algebraMap ℝ (even Q) r)) =
      LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε (algebraMap ℝ (even Q) r)) • 1 -
        evenHalfSpinAction o ρ ε (algebraMap ℝ (even Q) r)
    rw [reverseEven_algebraMap, AlgHom.commutes, Algebra.algebraMap_eq_smul_one,
      ← Complex.coe_smul, map_smul, LinearMap.trace_one, h₂, smul_eq_mul, Nat.cast_ofNat]
    module
  | add x y hx hy ihx ihy =>
    have h : (⟨x + y, Submodule.add_mem _ hx hy⟩ : even Q) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [h, map_add, map_add, ihx, ihy, map_add, map_add, add_smul]
    abel
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    -- `(c(m₁) c(m₂) x)* = x* (c(m₂) c(m₁))`, and the adjugate reverses products.
    have h : (⟨ι Q m₁ * ι Q m₂ * x, (Subalgebra.mul_mem _
        (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx)⟩ :
          even Q) = (even.ι Q).bilin m₁ m₂ * ⟨x, hx⟩ :=
      Subtype.ext (by rw [Subalgebra.coe_mul, coe_even_ι_bilin])
    rw [h, reverseEven_mul, reverseEven_ι, map_mul, map_mul, ih,
      evenHalfSpinAction_ι_bilin_swap o ρ ε hQ h₂,
      LinearMap.trace_mul_smul_one_sub_mul_of_finrank_eq_two h₂]

/-- Clifford conjugation acts as the adjugate on an eigenspace `W^ε` of `Γ` of complex dimension
two, pointwise: for an even element `x` and `ψ ∈ W^ε`, `ρ(x*) ψ = tr (ρ x) ψ - ρ x ψ`, where the
trace is that of `ρ x` on `W^ε`. -/
theorem map_star_apply_of_mem_even (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    {x : CliffordAlgebra Q} (hx : x ∈ even Q) (ψ : eigenspace (ρ (chirality Q o)) ε) :
    ρ (star x) ψ = LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε ⟨x, hx⟩) • (ψ : W) - ρ x ψ := by
  rw [← reverse_eq_star_of_mem_even ⟨x, hx⟩]
  simpa using congrArg (fun T ↦ (T ψ : W)) (evenHalfSpinAction_reverseEven o ρ ε hQ h₂ ⟨x, hx⟩)

/-- **The Clifford norm acts by the determinant** on an eigenspace `W^ε` of `Γ` of complex
dimension two: for an even element `x`, `x* x` acts on `W^ε` as `det (ρ x)`. -/
theorem evenHalfSpinAction_reverseEven_mul_self
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) (x : even Q) :
    evenHalfSpinAction o ρ ε (reverseEven Q x * x) =
      LinearMap.det (evenHalfSpinAction o ρ ε x) • 1 := by
  rw [← LinearMap.trace_smul_one_sub_mul_self_of_finrank_eq_two h₂,
    ← evenHalfSpinAction_reverseEven o ρ ε hQ h₂, ← map_mul]

/-- The Clifford norm acts by the determinant on an eigenspace `W^ε` of `Γ` of complex dimension
two, pointwise: for an even element `x` and `ψ ∈ W^ε`, `ρ(x* x) ψ = det (ρ x) ψ`. -/
theorem map_star_mul_self_apply_of_mem_even
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) {x : CliffordAlgebra Q}
    (hx : x ∈ even Q) (ψ : eigenspace (ρ (chirality Q o)) ε) :
    ρ (star x * x) ψ = LinearMap.det (evenHalfSpinAction o ρ ε ⟨x, hx⟩) • (ψ : W) := by
  rw [← reverse_eq_star_of_mem_even ⟨x, hx⟩]
  simpa using congrArg (fun T ↦ (T ψ : W))
    (evenHalfSpinAction_reverseEven_mul_self o ρ ε hQ h₂ ⟨x, hx⟩)

end EvenAction

variable (hQ : ∀ v, Q v = -‖v‖ ^ 2)
include hQ

section Module

variable {W : Type*} [AddCommGroup W] [Module ℂ W] {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

omit hQ in
/-- Clifford multiplication exchanges the eigenspaces of `Γ`: `c(v)` maps the `ε`-eigenspace into
the `-ε`-eigenspace. In particular it maps `W⁺` to `W⁻` and `W⁻` to `W⁺`. -/
theorem map_ι_apply_mem_eigenspace_chirality_neg {ε : ℂ} {ψ : W}
    (hψ : ψ ∈ eigenspace (ρ (chirality Q o)) ε) (v : V) :
    ρ (ι Q v) ψ ∈ eigenspace (ρ (chirality Q o)) (-ε) := by
  rw [mem_eigenspace_iff] at hψ ⊢
  rw [← Module.End.mul_apply, ← map_mul, chirality_mul_ι o, map_neg, map_mul,
    LinearMap.neg_apply, Module.End.mul_apply, hψ, map_smul, neg_smul]

variable [FiniteDimensional ℂ W]

/-- Clifford multiplication by a nonzero vector embeds the `ε`-eigenspace of `Γ` into the
`-ε`-eigenspace. -/
private theorem finrank_eigenspace_chirality_le_neg (ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W)
    (ε : ℂ) :
    finrank ℂ (eigenspace (ρ (chirality Q o)) ε) ≤
      finrank ℂ (eigenspace (ρ (chirality Q o)) (-ε)) := by
  have : Nontrivial V := Module.nontrivial_of_finrank_eq_succ (Fact.out : finrank ℝ V = 4)
  obtain ⟨v, hv⟩ := exists_ne (0 : V)
  have hinj := map_ι_injective ρ (v := v) (by simpa [hQ] using hv)
  exact LinearMap.finrank_le_finrank_of_injective
    (f := (ρ (ι Q v)).restrict fun _ hξ ↦ map_ι_apply_mem_eigenspace_chirality_neg o hξ v)
    fun ψ φ h ↦ Subtype.ext (hinj (congrArg Subtype.val h))

variable (ρ) in
/-- The two eigenspaces of `Γ` have the same dimension: `dim W⁻ = dim W⁺`. -/
theorem finrank_eigenspace_chirality_neg (ε : ℂ) :
    finrank ℂ (eigenspace (ρ (chirality Q o)) (-ε)) =
      finrank ℂ (eigenspace (ρ (chirality Q o)) ε) := by
  refine le_antisymm ?_ (finrank_eigenspace_chirality_le_neg o hQ ρ ε)
  have h := finrank_eigenspace_chirality_le_neg o hQ ρ (-ε)
  rwa [neg_neg] at h

/-- **Clifford multiplication by a nonzero spinor is a real isomorphism.** For a nonzero `ψ` in
the `ε`-eigenspace of `Γ`, when that eigenspace has complex dimension two, the real-linear map
`v ↦ c(v) ψ` is an isomorphism from `V` onto the `-ε`-eigenspace. For `ε = 1` this identifies
`V` with `W⁻`. -/
def cliffordMulEquiv {ε : ℂ} {ψ : W} (hψ : ψ ∈ eigenspace (ρ (chirality Q o)) ε) (hψ₀ : ψ ≠ 0)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) :
    V ≃ₗ[ℝ] eigenspace (ρ (chirality Q o)) (-ε) :=
  LinearMap.linearEquivOfInjective
    { toFun v := ⟨ρ (ι Q v) ψ, map_ι_apply_mem_eigenspace_chirality_neg o hψ v⟩
      map_add' v w := by ext; simp
      map_smul' r v := by ext; simp }
    (fun v w h ↦ map_ι_apply_left_injective ρ (fun v hv ↦ by simpa [hQ] using hv) hψ₀
      (congrArg Subtype.val h))
    (by rw [finrank_real_of_complex, finrank_eigenspace_chirality_neg o hQ ρ, h₂,
      (Fact.out : finrank ℝ V = 4)])

/-- `cliffordMulEquiv` is Clifford multiplication: it sends `v` to `c(v) ψ`. -/
@[simp]
theorem coe_cliffordMulEquiv_apply {ε : ℂ} {ψ : W} (hψ : ψ ∈ eigenspace (ρ (chirality Q o)) ε)
    (hψ₀ : ψ ≠ 0) (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) (v : V) :
    (cliffordMulEquiv o hQ hψ hψ₀ h₂ v : W) = ρ (ι Q v) ψ :=
  (rfl)

end Module

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W}

/-- If a spinor `χ` in the `-ε`-eigenspace of `Γ` is real-orthogonal to every Clifford multiple
`c(v) ψ` of a nonzero `ψ` in a two-dimensional `ε`-eigenspace, then `χ = 0`. For `ε = 1`: a
negative spinor with `Re ⟪c(v) ψ, χ⟫ = 0` for all `v` vanishes when the positive spinor `ψ` is
nonzero. -/
theorem eq_zero_of_forall_re_inner_map_ι_apply_eq_zero {ε : ℂ} {ψ χ : W}
    (hψ : ψ ∈ eigenspace (ρ (chirality Q o)) ε) (hψ₀ : ψ ≠ 0)
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (hχ : χ ∈ eigenspace (ρ (chirality Q o)) (-ε)) (h : ∀ v, (⟪ρ (ι Q v) ψ, χ⟫_ℂ).re = 0) :
    χ = 0 := by
  -- Write `χ = c(v) ψ` by surjectivity; then `‖χ‖² = Re ⟪χ, χ⟫ = 0`.
  set e := cliffordMulEquiv o hQ hψ hψ₀ h₂
  have hv := coe_cliffordMulEquiv_apply o hQ hψ hψ₀ h₂ (e.symm ⟨χ, hχ⟩)
  rw [LinearEquiv.apply_symm_apply] at hv
  have hχ₀ := h (e.symm ⟨χ, hχ⟩)
  rw [← hv, ← RCLike.re_to_complex, inner_self_eq_norm_sq] at hχ₀
  exact norm_eq_zero.1 (pow_eq_zero_iff two_ne_zero |>.1 hχ₀)

end CliffordAlgebra
