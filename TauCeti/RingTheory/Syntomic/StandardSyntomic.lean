/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.RingTheory.Extension.Presentation.Basic
public import Mathlib.RingTheory.Flat.Basic
public import Mathlib.RingTheory.LocalRing.ResidueField.Fiber
import Mathlib.RingTheory.KrullDimension.Polynomial
import Mathlib.RingTheory.TensorProduct.MvPolynomial
import TauCeti.RingTheory.KrullDimension.FiniteType

/-!
# Standard syntomic algebras

An `R`-algebra `S` is a *relative global complete intersection* if it has a presentation
`S = R[x₁, …, x_m] ⧸ (f₁, …, f_c)` such that every nonempty fibre `κ(p) ⊗[R] S` has Krull
dimension `m - c`; it is *standard syntomic* if moreover `S` is flat over `R`. Standard syntomic
algebras are the local models of syntomic morphisms (flat, locally finitely presented local
complete intersections): a ring map is syntomic exactly when it is standard syntomic locally on the
source. Standard smooth algebras and the local model `R[x, y] ⧸ (xy - a)` of a node are standard
syntomic, and a family of nodal curves is a syntomic morphism of relative dimension one.

We record the relative dimension `m - c`, which is the dimension of the nonempty fibres, and
require `m = n + c` for a presentation with `m` generators and `c` relations. Note that Mathlib's
`Algebra.Presentation.dimension` is the truncated difference `m - c`; demanding `m = n + c`
instead excludes presentations with more relations than generators, so that, for example,
`k[x, y] ⧸ (x², xy, y²)`, which is flat over the field `k` with fibre of dimension zero but is not
a complete intersection, is not standard syntomic of relative dimension zero.

## Main definitions

* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension n R S`: `S` is flat over `R`, has a
  finite presentation with `n + c` generators and `c` relations, and every nontrivial fibre
  `κ(p) ⊗[R] S` has Krull dimension `n`.

## Main results

* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.ringKrullDim_tensorProduct_of_field`:
  the dimension condition holds for all fibres over fields, not just over residue fields: if
  `R → K` is a ring map to a field and `K ⊗[R] S` is nontrivial, it has Krull dimension `n`.
* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.baseChange`: standard syntomic algebras of
  relative dimension `n` are stable under arbitrary base change.
* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.of_algEquiv`: invariance under
  isomorphism.
* `TauCeti.Algebra.IsStandardSyntomicOfRelativeDimension.mvPolynomial`: a polynomial algebra in
  finitely many variables is standard syntomic of relative dimension the number of variables.

## References

* The Stacks Project, Commutative Algebra, Section *Syntomic morphisms*: the definitions of
  relative global complete intersections and of standard syntomic ring maps, and the
  characterization of syntomic ring maps as those that are standard syntomic locally on the source.
* The shape of the definition, a class asserting the existence of a presentation with a prescribed
  number of generators and relations, and its basic API (`mvPolynomial`, `mvPolynomial_fin`,
  `baseChange`) are modelled on Mathlib's `Algebra.IsStandardSmoothOfRelativeDimension` in
  `Mathlib/RingTheory/Smooth/StandardSmooth.lean`, by Jung Tao Cheng, Christian Merten and
  Andrew Yang.
-/

public section

open TensorProduct

namespace TauCeti

namespace Algebra

universe u v w

attribute [local instance] Fintype.ofFinite

variable (n : ℕ) (R : Type u) (S : Type v) [CommRing R] [CommRing S] [Algebra R S]

/-- An `R`-algebra `S` is **standard syntomic of relative dimension `n`** if it is flat over `R`
and has a finite presentation `S = R[x₁, …, x_{n+c}] ⧸ (f₁, …, f_c)` which is a relative global
complete intersection: every nontrivial fibre `κ(p) ⊗[R] S` over a prime `p` of `R` has Krull
dimension `n`. The fibre condition does not depend on the presentation. -/
class IsStandardSyntomicOfRelativeDimension : Prop where
  /-- A standard syntomic algebra is flat. -/
  flat : Module.Flat R S
  /-- A presentation with `n + c` generators and `c` relations. -/
  exists_presentation : ∃ (ι σ : Type) (_ : Finite ι) (_ : Finite σ)
    (_ : _root_.Algebra.Presentation R S ι σ), Nat.card ι = n + Nat.card σ
  /-- Every nonempty fibre has Krull dimension `n`. -/
  ringKrullDim_fiber (p : Ideal R) [p.IsPrime] [Nontrivial (p.Fiber S)] :
    ringKrullDim (p.Fiber S) = n

variable {n R S}

/-- A finite presentation of a flat algebra with `n + c` generators and `c` relations, all of whose
nontrivial fibres have Krull dimension `n`, exhibits it as standard syntomic of relative dimension
`n`. -/
theorem _root_.Algebra.Presentation.isStandardSyntomicOfRelativeDimension [Module.Flat R S]
    {ι : Type w} {σ : Type*} [Finite ι] [Finite σ] (P : _root_.Algebra.Presentation R S ι σ)
    (hP : Nat.card ι = n + Nat.card σ)
    (hfib : ∀ (p : Ideal R) [p.IsPrime] [Nontrivial (p.Fiber S)], ringKrullDim (p.Fiber S) = n) :
    IsStandardSyntomicOfRelativeDimension n R S where
  flat := inferInstance
  exists_presentation := ⟨_, _, inferInstance, inferInstance,
    P.reindex (Fintype.equivFin ι).symm (Fintype.equivFin σ).symm, by simpa using hP⟩
  ringKrullDim_fiber := hfib

namespace IsStandardSyntomicOfRelativeDimension

variable [h : IsStandardSyntomicOfRelativeDimension n R S]

include h in
/-- A standard syntomic algebra is of finite presentation. -/
theorem finitePresentation : _root_.Algebra.FinitePresentation R S := by
  obtain ⟨ι, σ, _, _, P, -⟩ := h.exists_presentation
  exact P.finitePresentation_of_isFinite

include h in
/-- Every fibre of a standard syntomic algebra of relative dimension `n` has Krull dimension at
most `n`; the empty fibres have dimension `⊥`. -/
theorem ringKrullDim_fiber_le (p : Ideal R) [p.IsPrime] : ringKrullDim (p.Fiber S) ≤ n := by
  cases subsingleton_or_nontrivial (p.Fiber S)
  · simp [ringKrullDim_eq_bot_of_subsingleton]
  · exact (h.ringKrullDim_fiber p).le

include h in
/-- The fibres of a standard syntomic algebra of relative dimension `n` over arbitrary fields have
Krull dimension `n`: if `R → K` is a ring map to a field and `K ⊗[R] S` is nontrivial, then it has
Krull dimension `n`. -/
theorem ringKrullDim_tensorProduct_of_field (K : Type w) [Field K] [Algebra R K]
    [Nontrivial (K ⊗[R] S)] : ringKrullDim (K ⊗[R] S) = n := by
  have := h.finitePresentation
  -- The map `R → K` factors through the residue field `κ(p)` of its kernel `p`.
  let p := RingHom.ker (algebraMap R K)
  have : p.IsPrime := RingHom.ker_isPrime _
  let φ : p.ResidueField →+* K := Ideal.ResidueField.lift p (algebraMap R K) le_rfl fun r hr ↦
    (IsUnit.mk0 _ hr : IsUnit (algebraMap R K r))
  let : Algebra p.ResidueField K := φ.toAlgebra
  have : IsScalarTower R p.ResidueField K := .of_algebraMap_eq fun r ↦ by
    rw [RingHom.algebraMap_toAlgebra]
    exact (Ideal.ResidueField.lift_algebraMap p (algebraMap R K) _ _ r).symm
  -- Hence `K ⊗[R] S = K ⊗[κ(p)] (κ(p) ⊗[R] S)`, and extending the base field does not change
  -- the Krull dimension.
  let e : K ⊗[p.ResidueField] p.Fiber S ≃ₐ[K] K ⊗[R] S :=
    _root_.Algebra.TensorProduct.cancelBaseChange R p.ResidueField K K S
  have hdim : ringKrullDim (K ⊗[R] S) = ringKrullDim (p.Fiber S) :=
    (ringKrullDim_eq_of_ringEquiv e.toRingEquiv).symm.trans
      (ringKrullDim_tensorProduct_field_of_finiteType K (p.Fiber S))
  cases subsingleton_or_nontrivial (p.Fiber S) with
  | inl hF =>
    rw [ringKrullDim_eq_bot_of_subsingleton (R := p.Fiber S), ringKrullDim_eq_bot_iff_subsingleton]
      at hdim
    exact absurd hdim (not_subsingleton _)
  | inr hF => rw [hdim, h.ringKrullDim_fiber p]

include h in
/-- Standard syntomic algebras of relative dimension `n` are invariant under isomorphism. -/
theorem of_algEquiv {S' : Type*} [CommRing S'] [Algebra R S'] (e : S ≃ₐ[R] S') :
    IsStandardSyntomicOfRelativeDimension n R S' := by
  have := h.flat
  have : Module.Flat R S' := .of_linearEquiv e.symm.toLinearEquiv
  obtain ⟨ι, σ, _, _, P, hP⟩ := h.exists_presentation
  refine (P.ofAlgEquiv e).isStandardSyntomicOfRelativeDimension hP fun p _ _ ↦ ?_
  let f : p.Fiber S ≃ₐ[R] p.Fiber S' := _root_.Algebra.TensorProduct.congr .refl e
  have : Nontrivial (p.Fiber S) := f.toEquiv.nontrivial
  rw [← ringKrullDim_eq_of_ringEquiv f.toRingEquiv, h.ringKrullDim_fiber p]

include h in
/-- Standard syntomic algebras of relative dimension `n` are stable under base change. -/
instance baseChange (T : Type w) [CommRing T] [Algebra R T] :
    IsStandardSyntomicOfRelativeDimension n T (T ⊗[R] S) := by
  have := h.flat
  obtain ⟨ι, σ, _, _, P, hP⟩ := h.exists_presentation
  refine (P.baseChange T).isStandardSyntomicOfRelativeDimension hP fun q _ _ ↦ ?_
  -- The fibre of `T ⊗[R] S` at `q` is the fibre of `S` over the field `κ(q)`.
  let e : q.Fiber (T ⊗[R] S) ≃ₐ[q.ResidueField] q.ResidueField ⊗[R] S :=
    _root_.Algebra.TensorProduct.cancelBaseChange R T q.ResidueField q.ResidueField S
  have : Nontrivial (q.ResidueField ⊗[R] S) := e.symm.toEquiv.nontrivial
  rw [ringKrullDim_eq_of_ringEquiv e.toRingEquiv, h.ringKrullDim_tensorProduct_of_field]

variable (R) in
/-- A polynomial algebra in finitely many variables indexed by `ι` is standard syntomic of
relative dimension `Nat.card ι`. -/
theorem mvPolynomial (ι : Type w) [Finite ι] :
    IsStandardSyntomicOfRelativeDimension (Nat.card ι) R (MvPolynomial ι R) :=
  (_root_.Algebra.Presentation.mvPolynomial.{0} R ι).isStandardSyntomicOfRelativeDimension
    (by simp) fun p _ _ ↦ by
      -- The fibre over `p` is the polynomial algebra over the residue field `κ(p)`.
      rw [ringKrullDim_eq_of_ringEquiv (MvPolynomial.algebraTensorAlgEquiv R _).toRingEquiv,
        MvPolynomial.ringKrullDim_of_isNoetherianRing_of_finite, ringKrullDim_eq_zero_of_field,
        zero_add]

variable (n R) in
/-- A polynomial algebra in `n` variables is standard syntomic of relative dimension `n`. -/
instance mvPolynomial_fin : IsStandardSyntomicOfRelativeDimension n R (MvPolynomial (Fin n) R) := by
  simpa using mvPolynomial R (Fin n)

end IsStandardSyntomicOfRelativeDimension

end Algebra

end TauCeti
