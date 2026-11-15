/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Dimension.Constructions
public import Mathlib.LinearAlgebra.Finsupp.Supported

/-!
# The chain complex of a graded free module with a degree-lowering differential

Let `ι` be a set of generators graded by `deg : ι → α`, with `α` for instance `ℕ` or `ℤ`, and let
`d` be an endomorphism of the free module `ι →₀ R` which squares to zero and lowers the degree by
one: the coefficient of `j` in `d i` vanishes unless `deg i = deg j + 1`. Then `d` maps the chains
supported on generators of degree `n + 1` to the chains supported on generators of degree `n`
(`ChainComplex.mapsTo_supported_preimage_singleton`), and these submodules, with the restrictions
of `d`, form a chain complex `ChainComplex.ofGradedFinsupp` indexed by `α`. Its term in degree `n`
is free on the generators of degree `n` (`ChainComplex.ofGradedFinsuppXEquiv`), so over a ring with
the strong rank condition it has their number as its rank when they are finitely many
(`ChainComplex.finrank_ofGradedFinsupp_X`).

This is how Morse and Floer complexes arise: the generators are the critical points, or the
intersection points, the degree is the Morse or Maslov index, and the coefficients of `d` count
trajectories, or holomorphic strips, between generators of consecutive degree. The differential is
most naturally defined, and `d ∘ d = 0` most naturally proved, on all chains at once, ignoring the
grading; this file then produces the graded complex, whose homology is the Morse or Floer homology.
-/

public section

open CategoryTheory Finsupp Set

universe u v w

namespace ChainComplex

variable {R : Type u} [Ring R] {ι : Type v} {α : Type w} [AddRightCancelSemigroup α] [One α]
  [DecidableEq α] (deg : ι → α) (d : (ι →₀ R) →ₗ[R] ι →₀ R)

omit [DecidableEq α] in
variable {deg d} in
/-- If `d` lowers the degree of every generator by one, it maps the chains supported on
generators of degree `n + 1` to the chains supported on generators of degree `n`. -/
theorem mapsTo_supported_preimage_singleton
    (hd : ∀ i j, d (single i 1) j ≠ 0 → deg i = deg j + 1) (n : α) :
    MapsTo d (supported R R (deg ⁻¹' {n + 1})) (supported R R (deg ⁻¹' {n})) := by
  intro x hx
  rw [SetLike.mem_coe, supported_eq_span_single] at hx
  refine (Submodule.map_span_le d _ _).2 ?_ (Submodule.mem_map_of_mem hx)
  -- `d` sends each generator of degree `n + 1` to a chain supported in degree `n`.
  rintro _ ⟨i, hi, rfl⟩
  refine (mem_supported _ _).2 fun j hj ↦ ?_
  simp only [mem_preimage, mem_singleton_iff] at hi ⊢
  exact add_right_cancel ((hd i j (mem_support_iff.1 hj)).symm.trans hi)

/-- **The chain complex of a graded free module.** Let `d` be an endomorphism of `ι →₀ R` with
`d ∘ d = 0` such that the coefficient of `j` in `d i` vanishes unless `deg i = deg j + 1`. The
chain complex whose term in degree `n` is the submodule of chains supported on the generators of
degree `n`, with differentials the restrictions of `d`. -/
@[expose] noncomputable def ofGradedFinsupp (hd : ∀ i j, d (single i 1) j ≠ 0 → deg i = deg j + 1)
    (hdd : d ∘ₗ d = 0) : ChainComplex (ModuleCat.{max u v} R) α :=
  of (fun n ↦ ModuleCat.of R (supported R R (deg ⁻¹' {n})))
    (fun n ↦ ModuleCat.ofHom (d.restrict (mapsTo_supported_preimage_singleton hd n)))
    fun _ ↦ ModuleCat.hom_ext <| LinearMap.ext fun x ↦ Subtype.ext <| LinearMap.congr_fun hdd x

variable (hd : ∀ i j, d (single i 1) j ≠ 0 → deg i = deg j + 1) (hdd : d ∘ₗ d = 0)

/-- The term of degree `n` of `ChainComplex.ofGradedFinsupp` is the module of chains supported on
the generators of degree `n`. -/
theorem ofGradedFinsupp_X (n : α) :
    (ofGradedFinsupp deg d hd hdd).X n = ModuleCat.of R (supported R R (deg ⁻¹' {n})) :=
  (rfl)

/-- The differential of `ChainComplex.ofGradedFinsupp` from degree `n + 1` to degree `n` is the
restriction of `d`. -/
@[simp]
theorem coe_ofGradedFinsupp_d_hom_apply (n : α) (x : supported R R (deg ⁻¹' {n + 1})) :
    Subtype.val (p := (· ∈ supported R R (deg ⁻¹' {n})))
      (((ofGradedFinsupp deg d hd hdd).d (n + 1) n).hom x) = d x := by
  simp only [ofGradedFinsupp, of_d, ModuleCat.hom_ofHom]
  -- The restriction of `d` to submodules acts as `d` on the underlying chains.
  rfl

/-- The term of degree `n` of `ChainComplex.ofGradedFinsupp` is the free module on the generators
of degree `n`. -/
noncomputable def ofGradedFinsuppXEquiv (n : α) :
    (ofGradedFinsupp deg d hd hdd).X n ≃ₗ[R] (deg ⁻¹' {n} →₀ R) :=
  supportedEquivFinsupp _

/-- The identification of the term of degree `n` of `ChainComplex.ofGradedFinsupp` with the free
module on the generators of degree `n` keeps the coefficients of a chain. -/
@[simp]
theorem ofGradedFinsuppXEquiv_apply (n : α) (x : supported R R (deg ⁻¹' {n})) (i : deg ⁻¹' {n}) :
    ofGradedFinsuppXEquiv deg d hd hdd n x i = (x : ι →₀ R) i :=
  (rfl)

instance (n : α) : Module.Free R ((ofGradedFinsupp deg d hd hdd).X n) :=
  .of_equiv (ofGradedFinsuppXEquiv deg d hd hdd n).symm

instance (n : α) [Finite (deg ⁻¹' {n})] : Module.Finite R ((ofGradedFinsupp deg d hd hdd).X n) :=
  .equiv (ofGradedFinsuppXEquiv deg d hd hdd n).symm

/-- Over a ring with the strong rank condition, the term of degree `n` of
`ChainComplex.ofGradedFinsupp` has rank the number of generators of degree `n`, when they are
finitely many. -/
theorem finrank_ofGradedFinsupp_X [StrongRankCondition R] (n : α) [Finite (deg ⁻¹' {n})] :
    Module.finrank R ((ofGradedFinsupp deg d hd hdd).X n) = Nat.card (deg ⁻¹' {n}) := by
  have := Fintype.ofFinite (deg ⁻¹' {n})
  rw [(ofGradedFinsuppXEquiv deg d hd hdd n).finrank_eq, Module.finrank_finsupp_self,
    Nat.card_eq_fintype_card]

/-- The term of `ChainComplex.ofGradedFinsupp` in a degree without generators is zero. -/
theorem isZero_ofGradedFinsupp_X {n : α} (hn : ∀ i, deg i ≠ n) :
    Limits.IsZero ((ofGradedFinsupp deg d hd hdd).X n) := by
  have : IsEmpty (deg ⁻¹' {n}) := ⟨fun i ↦ hn i i.2⟩
  have := (ofGradedFinsuppXEquiv deg d hd hdd n).toEquiv.subsingleton
  exact ModuleCat.isZero_of_subsingleton _

end ChainComplex
