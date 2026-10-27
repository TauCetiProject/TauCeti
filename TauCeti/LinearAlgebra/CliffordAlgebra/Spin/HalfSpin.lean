/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Complex.Circle
public import Mathlib.Analysis.InnerProductSpace.Adjoint
public import Mathlib.RepresentationTheory.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Chirality
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Basic
public import TauCeti.LinearAlgebra.CliffordAlgebra.Spin.Kernel
-- Private: the adjoint, orthogonality, conjugation and adjugate facts are used only in proofs.
import TauCeti.LinearAlgebra.CliffordAlgebra.Hermitian
import TauCeti.LinearAlgebra.CliffordAlgebra.OrthonormalBasis
import TauCeti.LinearAlgebra.CliffordAlgebra.Star
import TauCeti.LinearAlgebra.End.Adjugate

/-!
# The half-spin representations of `Spin(4)` and `Spinᶜ(4)`

Let `V` be an oriented real inner product space of dimension four, `Q v = -‖v‖²`, and let `W` be
a finite-dimensional complex vector space with a real algebra map
`ρ : CliffordAlgebra Q → End_ℂ W`. The chirality element `Γ` (`CliffordAlgebra.chirality`)
commutes with every even Clifford element, so the even subalgebra, and with it the Spin group
`spinGroup Q`, acts on each eigenspace `W^ε` of `Γ`; for `ε = ±1` these are the half-spinors
`W^±`, and `ε = 1` is `CliffordAlgebra.positiveHalfSpinors o ρ`. Twisting by a unit complex
scalar gives the action `(s, z) ↦ z ρ(s)` of `Spin(4) × U(1)`. As `(-1, -1)` acts trivially, it
descends to the half-spin representations `ρ^±([s, z]) = z ρ^±(s)` of
`Spinᶜ(4) = (Spin(4) × U(1)) / {±(1, 1)}`, the structure group of the spinor bundles of a `Spinᶜ`
four-manifold.

When `W^ε` has complex dimension two, Clifford conjugation `star` acts on it as the adjugate: for
an even element `x`, `ρ(x*) = tr(ρ x) - ρ x` on `W^ε`. This holds on the generators `c(u) c(v)`,
whose trace on `W^ε` is `-2 ⟪u, v⟫`, and propagates because both sides reverse products.
Consequently `ρ(x* x) = det(ρ x)` on `W^ε`, so every Spin element acts with determinant one, and
`[s, z]` acts with determinant `z²`: the determinant line of `W^±` is the square of the twisting
circle. If `W` is moreover a Hermitian Clifford module, the generators acting skew-adjointly, both
representations are unitary.

## Main definitions

* `CliffordAlgebra.evenHalfSpinAction o ρ ε`: the even Clifford subalgebra acting on the
  `ε`-eigenspace of `Γ`.
* `CliffordAlgebra.halfSpinRep o ρ ε`: the representation of `spinGroup Q` on that eigenspace.
* `CliffordAlgebra.spinCHalfSpinRep o ρ ε`: the representation `(s, z) ↦ z ρ(s)` of
  `spinGroup Q × Circle` on that eigenspace.

## Main results

* `CliffordAlgebra.trace_evenHalfSpinAction_ι_bilin`: `tr (c(u) c(v)) = -⟪u, v⟫ dim W^ε`.
* `CliffordAlgebra.map_star_apply_of_mem_even`: in complex dimension two, Clifford conjugation
  acts on `W^ε` as the adjugate, and `CliffordAlgebra.map_star_mul_self_apply_of_mem_even`:
  `x* x` acts by `det (ρ x)`.
* `CliffordAlgebra.det_halfSpinRep`: Spin elements act on a two-dimensional `W^ε` with
  determinant one.
* `CliffordAlgebra.inner_halfSpinRep_apply_halfSpinRep_apply`: on a Hermitian Clifford module the
  Spin action is unitary.
* `CliffordAlgebra.spinCHalfSpinRep_negOne_neg_one`: `(-1, -1)` acts trivially, so the twisted
  action descends to `Spinᶜ(4)`.
* `CliffordAlgebra.det_spinCHalfSpinRep`: `(s, z)` acts with determinant `z²`, and
  `CliffordAlgebra.inner_spinCHalfSpinRep_apply_spinCHalfSpinRep_apply`: the twisted action is
  unitary.

## References

* H. B. Lawson and M.-L. Michelsohn, *Spin Geometry* (1989), Chapter I, §5 and Appendix D.
* J. W. Morgan, *The Seiberg–Witten equations and applications to the topology of smooth
  four-manifolds*, Mathematical Notes 44, Princeton University Press, 1996, §3.1.
-/

public section

noncomputable section

namespace CliffordAlgebra

open Module Module.End
open scoped InnerProductSpace RealInnerProductSpace

variable {V : Type*} [NormedAddCommGroup V] [InnerProductSpace ℝ V] [Fact (finrank ℝ V = 4)]
  {Q : QuadraticForm ℝ V} (o : Orientation ℝ V (Fin 4))

/-- The dimension `Fact` makes the oriented four-space finite-dimensional. -/
local instance : FiniteDimensional ℝ V := .of_fact_finrank_eq_succ 3

section Module

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

/-- **The half-spin representation of the Spin group** on the `ε`-eigenspace of `Γ`, the
restriction of the Clifford action along `spinGroup Q ⊆ even Q`. -/
def halfSpinRep : Representation ℂ (spinGroup Q) (eigenspace (ρ (chirality Q o)) ε) :=
  (evenHalfSpinAction o ρ ε).toMonoidHom.comp (spinGroupToEven Q)

/-- `halfSpinRep` is the restriction of the Clifford action. -/
@[simp]
theorem coe_halfSpinRep_apply (s : spinGroup Q) (ψ : eigenspace (ρ (chirality Q o)) ε) :
    (halfSpinRep o ρ ε s ψ : W) = ρ s ψ := by
  simp [halfSpinRep]

/-- **The half-spin representation of `Spinᶜ(4)`**, before passing to the quotient by
`{±(1, 1)}`: `(s, z)` acts on the `ε`-eigenspace of `Γ` by `z ρ(s)`. It is trivial on
`(-1, -1)` (`CliffordAlgebra.spinCHalfSpinRep_negOne_neg_one`). -/
def spinCHalfSpinRep :
    Representation ℂ (spinGroup Q × Circle) (eigenspace (ρ (chirality Q o)) ε) where
  toFun p := (p.2 : ℂ) • halfSpinRep o ρ ε p.1
  map_one' := by simp
  map_mul' p q := by
    simp only [Prod.fst_mul, Prod.snd_mul, map_mul, Circle.coe_mul, mul_smul_comm, smul_mul_assoc,
      smul_smul, mul_comm]

/-- `(s, z)` acts by `z ρ(s)`. -/
@[simp]
theorem spinCHalfSpinRep_apply (s : spinGroup Q) (z : Circle) :
    spinCHalfSpinRep o ρ ε (s, z) = (z : ℂ) • halfSpinRep o ρ ε s :=
  (rfl)

/-- **The twisted action descends to `Spinᶜ(4)`**: the central element `(-1, -1)` of
`spinGroup Q × Circle` acts trivially. -/
theorem spinCHalfSpinRep_negOne_neg_one (hQ₀ : Q ≠ 0) :
    spinCHalfSpinRep o ρ ε (spinGroup.negOne Q hQ₀, -1) = 1 := by
  ext ψ
  simp

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
  obtain ⟨e, he₀, hue, hve⟩ : ∃ e : V, e ≠ 0 ∧ ⟪u, e⟫ = 0 ∧ ⟪v, e⟫ = 0 := by
    classical
    set K := Submodule.span ℝ ((({u, v} : Finset V)) : Set V)
    have hK : finrank ℝ K ≤ 2 := (finrank_span_finset_le_card _).trans Finset.card_le_two
    have hKperp : Kᗮ ≠ ⊥ := by
      intro h
      have := K.finrank_add_finrank_orthogonal
      rw [h, finrank_bot, (Fact.out : finrank ℝ V = 4)] at this
      omega
    obtain ⟨e, he, he₀⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hKperp
    exact ⟨e, he₀, Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (by simp)) he,
      Submodule.inner_right_of_mem_orthogonal (Submodule.subset_span (by simp)) he⟩
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

omit hQ in
/-- A real scalar acts on an eigenspace of `Γ` as the corresponding complex scalar. -/
private theorem algebraMap_end_eq_ofReal_smul_one (r : ℝ) :
    algebraMap ℝ (Module.End ℂ (eigenspace (ρ (chirality Q o)) ε)) r = (r : ℂ) • 1 := by
  ext
  simp [Algebra.algebraMap_eq_smul_one]

variable [FiniteDimensional ℂ W]

omit [Fact (finrank ℝ V = 4)] in
/-- The Clifford relation for the even generators: `c(u) c(v) + c(v) c(u) = -2 ⟪u, v⟫`. -/
private theorem even_ι_bilin_add_swap (u v : V) :
    (even.ι Q).bilin u v + (even.ι Q).bilin v u = algebraMap ℝ (even Q) (-2 * ⟪u, v⟫) := by
  refine Subtype.ext ?_
  rw [Subalgebra.coe_add, Subalgebra.coe_algebraMap, coe_even_ι_bilin, coe_even_ι_bilin,
    ι_mul_ι_add_swap]
  congr 1
  simp only [QuadraticMap.polar, hQ, norm_add_sq_real]
  ring

/-- **The trace of `c(u) c(v)` on an eigenspace of `Γ`** is `-⟪u, v⟫` times its dimension. -/
theorem trace_evenHalfSpinAction_ι_bilin (u v : V) :
    LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε ((even.ι Q).bilin u v)) =
      -⟪u, v⟫ * finrank ℂ (eigenspace (ρ (chirality Q o)) ε) := by
  -- By symmetry, twice the trace is the trace of `c(u) c(v) + c(v) c(u) = -2 ⟪u, v⟫`.
  have h := congrArg (fun x ↦ LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε x))
    (even_ι_bilin_add_swap hQ u v)
  rw [map_add, map_add, ← trace_evenHalfSpinAction_ι_bilin_comm o ρ ε hQ u v, AlgHom.commutes,
    algebraMap_end_eq_ofReal_smul_one, map_smul, LinearMap.trace_one, smul_eq_mul] at h
  push_cast at h
  linear_combination h / 2

/-- In complex dimension two, `c(v) c(u)` acts on an eigenspace of `Γ` as the adjugate
`tr T - T` of the action `T` of `c(u) c(v)`. -/
private theorem evenHalfSpinAction_ι_bilin_swap
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) (u v : V) :
    evenHalfSpinAction o ρ ε ((even.ι Q).bilin v u) =
      LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε ((even.ι Q).bilin u v)) • 1 -
        evenHalfSpinAction o ρ ε ((even.ι Q).bilin u v) := by
  rw [trace_evenHalfSpinAction_ι_bilin o ρ ε hQ, h₂, eq_sub_iff_add_eq', ← map_add,
    even_ι_bilin_add_swap hQ, AlgHom.commutes, algebraMap_end_eq_ofReal_smul_one]
  push_cast
  ring_nf

/-- In complex dimension two, Clifford conjugation acts on an eigenspace of `Γ` as the adjugate,
`x* ↦ tr (ρ x) - ρ x`: both sides reverse products, and they agree on the generators. -/
private theorem evenHalfSpinAction_star
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) (x : CliffordAlgebra Q)
    (hx : x ∈ even Q) :
    evenHalfSpinAction o ρ ε ⟨star x, star_mem_even hx⟩ =
      LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε ⟨x, hx⟩) • 1 -
        evenHalfSpinAction o ρ ε ⟨x, hx⟩ := by
  induction x, hx using even_induction with
  | algebraMap r =>
    have hs : (⟨star (algebraMap ℝ _ r), star_mem_even (SetLike.algebraMap_mem_graded _ _)⟩ :
        even Q) = algebraMap ℝ (even Q) r := Subtype.ext (star_algebraMap r)
    have h : (⟨algebraMap ℝ _ r, SetLike.algebraMap_mem_graded _ _⟩ : even Q) =
        algebraMap ℝ (even Q) r := rfl
    rw [hs, h, AlgHom.commutes, algebraMap_end_eq_ofReal_smul_one, map_smul, LinearMap.trace_one,
      h₂, smul_eq_mul, Nat.cast_ofNat]
    module
  | add x y hx hy ihx ihy =>
    have h : (⟨star (x + y), star_mem_even (Submodule.add_mem _ hx hy)⟩ : even Q) =
        ⟨star x, star_mem_even hx⟩ + ⟨star y, star_mem_even hy⟩ := Subtype.ext (star_add x y)
    have h' : (⟨x + y, Submodule.add_mem _ hx hy⟩ : even Q) = ⟨x, hx⟩ + ⟨y, hy⟩ := rfl
    rw [h, h', map_add, ihx, ihy, map_add, map_add, add_smul]
    abel
  | ι_mul_ι_mul m₁ m₂ x hx ih =>
    -- `(c(m₁) c(m₂) x)* = x* (c(m₂) c(m₁))`, and the adjugate reverses products.
    have h : (⟨star (ι Q m₁ * ι Q m₂ * x), star_mem_even (Subalgebra.mul_mem _
        (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx)⟩ :
          even Q) = ⟨star x, star_mem_even hx⟩ * (even.ι Q).bilin m₂ m₁ := by
      refine Subtype.ext ?_
      simp [coe_even_ι_bilin, star_mul, mul_assoc]
    have h' : (⟨ι Q m₁ * ι Q m₂ * x, (Subalgebra.mul_mem _
        (ι_mul_ι_mem_evenOdd_zero Q m₁ m₂) hx)⟩ :
          even Q) = (even.ι Q).bilin m₁ m₂ * ⟨x, hx⟩ :=
      Subtype.ext (by rw [Subalgebra.coe_mul, coe_even_ι_bilin])
    rw [h, h', map_mul, map_mul, ih, evenHalfSpinAction_ι_bilin_swap o ρ ε hQ h₂,
      LinearMap.trace_mul_smul_one_sub_mul_of_finrank_eq_two h₂]

/-- **Clifford conjugation acts as the adjugate** on an eigenspace `W^ε` of `Γ` of complex
dimension two: for an even element `x` and `ψ ∈ W^ε`, `ρ(x*) ψ = tr (ρ x) ψ - ρ x ψ`, where the
trace is that of `ρ x` on `W^ε`. -/
theorem map_star_apply_of_mem_even (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    {x : CliffordAlgebra Q} (hx : x ∈ even Q) (ψ : eigenspace (ρ (chirality Q o)) ε) :
    ρ (star x) ψ = LinearMap.trace ℂ _ (evenHalfSpinAction o ρ ε ⟨x, hx⟩) • (ψ : W) - ρ x ψ := by
  simpa using congrArg (fun T ↦ (T ψ : W)) (evenHalfSpinAction_star o ρ ε hQ h₂ x hx)

/-- **The Clifford norm acts by the determinant** on an eigenspace `W^ε` of `Γ` of complex
dimension two: for an even element `x`, `x* x` acts on `W^ε` as `det (ρ x)`. -/
theorem map_star_mul_self_apply_of_mem_even
    (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2) {x : CliffordAlgebra Q}
    (hx : x ∈ even Q) (ψ : eigenspace (ρ (chirality Q o)) ε) :
    ρ (star x * x) ψ = LinearMap.det (evenHalfSpinAction o ρ ε ⟨x, hx⟩) • (ψ : W) := by
  have h := congrArg (· * evenHalfSpinAction o ρ ε ⟨x, hx⟩)
    (evenHalfSpinAction_star o ρ ε hQ h₂ x hx)
  simp only [← map_mul, LinearMap.trace_smul_one_sub_mul_self_of_finrank_eq_two h₂] at h
  simpa using congrArg (fun T ↦ (T ψ : W)) h

/-- **Spin elements act with determinant one** on an eigenspace of `Γ` of complex dimension
two: the half-spin representations of `Spin(4)` take values in the special linear group. -/
theorem det_halfSpinRep (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (s : spinGroup Q) : LinearMap.det (halfSpinRep o ρ ε s) = 1 := by
  have : Nontrivial (eigenspace (ρ (chirality Q o)) ε) :=
    Module.nontrivial_of_finrank_eq_succ h₂
  obtain ⟨ψ, hψ⟩ := exists_ne (0 : eigenspace (ρ (chirality Q o)) ε)
  have hs : halfSpinRep o ρ ε s = evenHalfSpinAction o ρ ε ⟨s, spinGroup.mem_even s.2⟩ :=
    congrArg (evenHalfSpinAction o ρ ε) (Subtype.ext (coe_spinGroupToEven_apply Q s))
  have h := map_star_mul_self_apply_of_mem_even o ρ ε hQ h₂ (spinGroup.mem_even s.2) ψ
  rw [← hs] at h
  rw [spinGroup.star_mul_self_of_mem s.2, map_one, Module.End.one_apply, eq_comm,
    ← sub_eq_zero] at h
  have h' : (LinearMap.det (halfSpinRep o ρ ε s) - 1) • (ψ : W) = 0 := by
    rw [sub_smul, one_smul]
    exact h
  exact sub_eq_zero.1 ((smul_eq_zero.1 h').resolve_right (by simpa using hψ))

/-- **The twisted action has determinant `z²`**: `(s, z)` acts on an eigenspace of `Γ` of
complex dimension two with determinant `z²`. So the determinant line of `W^±` is the square of the
twisting circle. -/
theorem det_spinCHalfSpinRep (h₂ : finrank ℂ (eigenspace (ρ (chirality Q o)) ε) = 2)
    (s : spinGroup Q) (z : Circle) :
    LinearMap.det (spinCHalfSpinRep o ρ ε (s, z)) = (z : ℂ) ^ 2 := by
  rw [spinCHalfSpinRep_apply, LinearMap.det_smul, h₂, det_halfSpinRep o ρ ε hQ h₂, mul_one]

end Module

section Hermitian

variable {W : Type*} [NormedAddCommGroup W] [InnerProductSpace ℂ W] [FiniteDimensional ℂ W]
  {ρ : CliffordAlgebra Q →ₐ[ℝ] Module.End ℂ W} (ε : ℂ)

/-- **The half-spin representations are unitary** on a Hermitian Clifford module, whose
generators act skew-adjointly: `⟪ρ(s) ψ, ρ(s) χ⟫ = ⟪ψ, χ⟫`. -/
theorem inner_halfSpinRep_apply_halfSpinRep_apply
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (s : spinGroup Q)
    (ψ χ : eigenspace (ρ (chirality Q o)) ε) :
    ⟪halfSpinRep o ρ ε s ψ, halfSpinRep o ρ ε s χ⟫_ℂ = ⟪ψ, χ⟫_ℂ := by
  rw [Submodule.coe_inner, Submodule.coe_inner, coe_halfSpinRep_apply, coe_halfSpinRep_apply,
    ← LinearMap.adjoint_inner_right, adjoint_map_eq_map_star hρ, ← Module.End.mul_apply,
    ← map_mul, spinGroup.star_mul_self_of_mem s.2, map_one, Module.End.one_apply]

/-- **The twisted half-spin representations are unitary** on a Hermitian Clifford module. -/
theorem inner_spinCHalfSpinRep_apply_spinCHalfSpinRep_apply
    (hρ : ∀ v, LinearMap.adjoint (ρ (ι Q v)) = -ρ (ι Q v)) (p : spinGroup Q × Circle)
    (ψ χ : eigenspace (ρ (chirality Q o)) ε) :
    ⟪spinCHalfSpinRep o ρ ε p ψ, spinCHalfSpinRep o ρ ε p χ⟫_ℂ = ⟪ψ, χ⟫_ℂ := by
  obtain ⟨s, z⟩ := p
  rw [spinCHalfSpinRep_apply, LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left,
    inner_smul_right, inner_halfSpinRep_apply_halfSpinRep_apply o ε hρ, ← mul_assoc,
    Complex.conj_mul', Circle.norm_coe, Complex.ofReal_one, one_pow, one_mul]

end Hermitian

end CliffordAlgebra
