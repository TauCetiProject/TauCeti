/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.FreeModule.PID
public import Mathlib.LinearAlgebra.FreeModule.StrongRankCondition
public import Mathlib.LinearAlgebra.Unimodular
public import Mathlib.RingTheory.LocalRing.Module
import Mathlib.LinearAlgebra.Projection
import TauCeti.LinearAlgebra.Basis.Fin

/-!
# Completing a unimodular vector to a basis over a PID or a local ring

A vector `v` of an `R`-module `M` is unimodular when some linear functional `f` takes the value
one at `v`. Then `M` is the internal direct sum of the line `R ∙ v` and the kernel of `f`
(`LinearMap.isCompl_span_singleton_ker`), so the quotient `M ⧸ R ∙ v` is a direct summand of `M`.
In particular it is projective when `M` is (`Module.IsUnimodular.projective_quotient`).

Over a local ring or a principal ideal domain, finite projective modules are free, so for `M`
finite and free the quotient `M ⧸ R ∙ v` is free as well
(`Module.IsUnimodular.free_quotient_of_isLocalRing`,
`Module.IsUnimodular.free_quotient_of_isPrincipalIdealRing`). Whenever the quotient is free, `v`
followed by lifts of a basis of the quotient is a basis of `M`: the quotient has rank one less than
`M`, and `v` is the first vector of a basis of `M` indexed by `Fin (n + 1)`. Mathlib proves the
last statement in rank two over every commutative ring (`Module.IsUnimodular.exists_basis_zero_eq`);
over a general commutative ring it fails in higher rank, because a stably free module need not be
free.

The main application is to an `R`-algebra `A` which is free of finite rank as an `R`-module. Its
unit is unimodular (`Module.Free.isUnimodular_one`), and the scalar map `r ↦ r • 1` is injective
when `A` is nonzero (`FaithfulSMul.algebraMap_injective`). Over a local ring or a principal ideal
domain, the quotient of `A` by its scalars `(1 : Submodule R A) = R ∙ 1` is free, its rank is one
less than that of `A` (`Module.Free.finrank_quotient_one_add_one`), and `1` is the first vector
of a basis of `A` (`Module.Free.exists_basis_zero_eq_one`). For a cubic ring over `ℤ` or `ℤ_[p]`
these are the bases `⟨1, ω, θ⟩` through which a binary cubic form is attached to the ring.

## Main results

* `LinearMap.isCompl_span_singleton_ker`: if `f v = 1`, then `R ∙ v` and `ker f` are
  complementary.
* `LinearMap.quotientSpanSingletonEquivKer`: if `f v = 1`, then `M ⧸ R ∙ v` is isomorphic to
  `ker f`, the class of `x` corresponding to `x - f x • v`.
* `Module.IsUnimodular.projective_quotient`: the quotient of a projective module by the line
  through a unimodular vector is projective.
* `Module.IsUnimodular.free_quotient_of_isLocalRing`,
  `Module.IsUnimodular.free_quotient_of_isPrincipalIdealRing`: over a local ring or a principal
  ideal domain, that quotient of a finite free module is free.
* `Module.IsUnimodular.finrank_quotient_add_one`,
  `Module.IsUnimodular.exists_basis_zero_eq_of_free_quotient`: when the quotient is free, it has
  rank one less, and the unimodular vector is the first vector of a basis.
* `Module.free_quotient_one_of_isLocalRing`, `Module.free_quotient_one_of_isPrincipalIdealRing`:
  over a local ring or a principal ideal domain, the quotient of a finite free algebra by its
  scalars is free.
* `Module.free_quotient_one_iff`: the quotients `A ⧸ (1 : Submodule R A)` and `A ⧸ R ∙ 1` are
  free together.
* `Module.Free.finrank_quotient_one_add_one`, `Module.Free.exists_basis_zero_eq_one`: when that
  quotient is free, it has rank one less than the algebra, and `1` is the first vector of a
  basis.

## References

* B. H. Gross and M. Lucianovic, *On cubic rings and quaternion rings*, J. Number Theory 129
  (2009), 1468–1478, Lemma 1.1 and its proof: over a principal ideal domain or a local ring, the
  quotient of a free algebra of finite rank by its scalars is free.
-/

public section

open Module

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M]

/-- If a linear functional `f` takes the value one at `v`, then the line `R ∙ v` and the kernel
of `f` are complementary submodules: every vector `x` is `f x • v` plus a vector of the kernel. -/
theorem LinearMap.isCompl_span_singleton_ker {f : M →ₗ[R] R} {v : M} (hf : f v = 1) :
    IsCompl (R ∙ v) (LinearMap.ker f) := by
  refine ⟨Submodule.disjoint_def.2 fun x hx hker ↦ ?_,
    Submodule.codisjoint_iff_exists_add_eq.2 fun x ↦
      ⟨f x • v, x - f x • v, Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v),
        by simp [hf], add_sub_cancel _ _⟩⟩
  obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.1 hx
  simp [hf] at hker
  simp [hker]

/-- If a linear functional `f` takes the value one at `v`, then the quotient `M ⧸ R ∙ v` is
isomorphic to the kernel of `f`: the class of `x` corresponds to `x - f x • v`, and the inverse is
induced by the inclusion of the kernel. -/
noncomputable def LinearMap.quotientSpanSingletonEquivKer {f : M →ₗ[R] R} {v : M} (hf : f v = 1) :
    (M ⧸ R ∙ v) ≃ₗ[R] LinearMap.ker f :=
  Submodule.quotientEquivOfIsCompl _ _ (LinearMap.isCompl_span_singleton_ker hf)

/-- The vector of `ker f` attached to a class of `M ⧸ R ∙ v` lies in that class. -/
@[simp]
theorem LinearMap.mk_quotientSpanSingletonEquivKer_apply {f : M →ₗ[R] R} {v : M} (hf : f v = 1)
    (x : M ⧸ R ∙ v) : Submodule.Quotient.mk (quotientSpanSingletonEquivKer hf x : M) = x :=
  Submodule.mk_quotientEquivOfIsCompl_apply _ x

/-- The class of `x` in `M ⧸ R ∙ v` corresponds to the vector `x - f x • v` of `ker f`. -/
@[simp]
theorem LinearMap.quotientSpanSingletonEquivKer_apply_mk {f : M →ₗ[R] R} {v : M} (hf : f v = 1)
    (x : M) : (quotientSpanSingletonEquivKer hf (Submodule.Quotient.mk x) : M) = x - f x • v := by
  have hx : x - f x • v ∈ LinearMap.ker f := by simp [hf]
  have hmk : (Submodule.Quotient.mk x : M ⧸ R ∙ v) = Submodule.Quotient.mk (x - f x • v) := by
    rw [Submodule.Quotient.eq, sub_sub_cancel]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  rw [hmk]
  exact congrArg Subtype.val (Submodule.quotientEquivOfIsCompl_apply_mk_right _ ⟨_, hx⟩)

/-- The inverse of `LinearMap.quotientSpanSingletonEquivKer` sends a vector of `ker f` to its class
in `M ⧸ R ∙ v`. -/
@[simp]
theorem LinearMap.quotientSpanSingletonEquivKer_symm_apply {f : M →ₗ[R] R} {v : M}
    (hf : f v = 1) (y : LinearMap.ker f) :
    (quotientSpanSingletonEquivKer hf).symm y = Submodule.Quotient.mk (y : M) :=
  Submodule.quotientEquivOfIsCompl_symm_apply _ _ _ y

end Ring

namespace Module.IsUnimodular

section Ring

variable {R M : Type*} [Ring R] [AddCommGroup M] [Module R M] {v : M}

/-- The quotient of a projective module by the line through a unimodular vector is projective:
it is isomorphic to the kernel of a functional taking the value one at the vector, which is a
direct summand. -/
theorem projective_quotient [Module.Projective R M] (hv : IsUnimodular R v) :
    Module.Projective R (M ⧸ R ∙ v) := by
  obtain ⟨f, hf⟩ := isUnimodular_iff.mp hv
  exact .of_split
    ((LinearMap.ker f).subtype ∘ₗ (LinearMap.quotientSpanSingletonEquivKer hf).toLinearMap)
    (R ∙ v).mkQ (LinearMap.ext fun x ↦ by simp)

/-- A unimodular vector `v` followed by lifts of the vectors of any basis `b` of `M ⧸ R ∙ v` is a
basis of `M`. -/
theorem exists_basis_finCons (hv : IsUnimodular R v) {m : ℕ} (b : Basis (Fin m) R (M ⧸ R ∙ v)) :
    ∃ e : Basis (Fin (m + 1)) R M, e 0 = v ∧ ∀ i, (R ∙ v).mkQ (e i.succ) = b i := by
  obtain ⟨f, hf⟩ := isUnimodular_iff.mp hv
  obtain ⟨e, he0, he⟩ := Basis.exists_basis_finCons_of_apply_eq_one hf
    (b.map (LinearMap.quotientSpanSingletonEquivKer hf))
  refine ⟨e, he0, fun i ↦ ?_⟩
  rw [he, Basis.map_apply, Submodule.mkQ_apply, LinearMap.mk_quotientSpanSingletonEquivKer_apply]

end Ring

section CommRing

variable {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] {v : M}

/-- Over a local ring, the quotient of a finite projective module by the line through a
unimodular vector is free. -/
theorem free_quotient_of_isLocalRing [IsLocalRing R] [Module.Finite R M] [Module.Projective R M]
    (hv : IsUnimodular R v) : Module.Free R (M ⧸ R ∙ v) :=
  have := hv.projective_quotient
  free_of_flat_of_isLocalRing

/-- Over a principal ideal domain, the quotient of a finite free module by the line through a
unimodular vector is free. -/
theorem free_quotient_of_isPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R M] [Module.Free R M] (hv : IsUnimodular R v) :
    Module.Free R (M ⧸ R ∙ v) := by
  obtain ⟨f, hf⟩ := isUnimodular_iff.mp hv
  -- The quotient is isomorphic to the kernel of `f`, a submodule of a finite free module.
  exact .of_equiv (LinearMap.quotientSpanSingletonEquivKer hf).symm

/-- If the quotient of a finite module by the line through a unimodular vector is free, its rank
is one less than that of the module. -/
theorem finrank_quotient_add_one [Nontrivial R] [Module.Finite R M] [Module.Free R (M ⧸ R ∙ v)]
    (hv : IsUnimodular R v) : finrank R (M ⧸ R ∙ v) + 1 = finrank R M := by
  obtain ⟨e, -, -⟩ := hv.exists_basis_finCons (finBasis R (M ⧸ R ∙ v))
  rw [finrank_eq_card_basis e, Fintype.card_fin]

/-- If the quotient of a finite module of rank `n + 1` by the line through a unimodular vector `v`
is free, then `v` is the first vector of a basis indexed by `Fin (n + 1)`. Over a local ring or a
principal ideal domain the quotient is free (`Module.IsUnimodular.free_quotient_of_isLocalRing`,
`Module.IsUnimodular.free_quotient_of_isPrincipalIdealRing`); in rank two `v` is the first vector
of a basis over every commutative ring (`Module.IsUnimodular.exists_basis_zero_eq`). -/
theorem exists_basis_zero_eq_of_free_quotient [Module.Finite R M] [Module.Free R (M ⧸ R ∙ v)]
    {n : ℕ} (hM : finrank R M = n + 1) (hv : IsUnimodular R v) :
    ∃ e : Basis (Fin (n + 1)) R M, e 0 = v := by
  -- Over the zero ring every module is zero, and has a basis indexed by any type.
  rcases subsingleton_or_nontrivial R with _ | _
  · have := Module.subsingleton R M
    exact ⟨.ofRepr (.ofSubsingleton _ _), Subsingleton.elim _ _⟩
  have hn : finrank R (M ⧸ R ∙ v) = n := by
    have := hv.finrank_quotient_add_one
    omega
  obtain ⟨e, he0, -⟩ := hv.exists_basis_finCons (finBasisOfFinrankEq R _ hn)
  exact ⟨e, he0⟩

end CommRing

end Module.IsUnimodular

/-! ### The quotient of a free algebra by its scalars -/

namespace Module

variable {R A : Type*} [CommRing R] [Ring A] [Algebra R A]

/-- The scalars `(1 : Submodule R A)` are the line `R ∙ 1`, so the two quotients are free
together. This moves the freeness instances below to `A ⧸ R ∙ 1`, the quotient in which
`Module.IsUnimodular.exists_basis_finCons` places the images of a basis. -/
theorem free_quotient_one_iff :
    Module.Free R (A ⧸ (1 : Submodule R A)) ↔ Module.Free R (A ⧸ R ∙ (1 : A)) := by
  rw [Submodule.one_eq_span]

/-- Over a local ring, the quotient of a finite free algebra by its scalars is free. -/
instance free_quotient_one_of_isLocalRing [IsLocalRing R] [Module.Finite R A] [Module.Free R A] :
    Module.Free R (A ⧸ (1 : Submodule R A)) := by
  cases subsingleton_or_nontrivial A
  · infer_instance
  exact free_quotient_one_iff.2 Module.Free.isUnimodular_one.free_quotient_of_isLocalRing

/-- Over a principal ideal domain, the quotient of a finite free algebra by its scalars is free. -/
instance free_quotient_one_of_isPrincipalIdealRing [IsDomain R] [IsPrincipalIdealRing R]
    [Module.Finite R A] [Module.Free R A] : Module.Free R (A ⧸ (1 : Submodule R A)) := by
  cases subsingleton_or_nontrivial A
  · infer_instance
  exact free_quotient_one_iff.2 Module.Free.isUnimodular_one.free_quotient_of_isPrincipalIdealRing

namespace Free

variable [Module.Free R A] [Module.Free R (A ⧸ (1 : Submodule R A))]

/-- The quotient of a nonzero finite free algebra by its scalars, when free (for instance over a
local ring or a principal ideal domain), has rank one less than the algebra. -/
theorem finrank_quotient_one_add_one [Module.Finite R A] [Nontrivial A] :
    finrank R (A ⧸ (1 : Submodule R A)) + 1 = finrank R A := by
  have : Nontrivial R := Module.nontrivial R A
  have : Module.Free R (A ⧸ R ∙ (1 : A)) := free_quotient_one_iff.1 ‹_›
  rw [Submodule.one_eq_span]
  exact isUnimodular_one.finrank_quotient_add_one

/-- In a free algebra of rank `n + 1` whose quotient by the scalars is free (for instance over a
local ring or a principal ideal domain), `1` is the first vector of a basis indexed by
`Fin (n + 1)`. -/
theorem exists_basis_zero_eq_one {n : ℕ} (hA : finrank R A = n + 1) :
    ∃ b : Basis (Fin (n + 1)) R A, b 0 = 1 := by
  rcases subsingleton_or_nontrivial R with _ | _
  · have := Module.subsingleton R A
    exact ⟨.ofRepr (.ofSubsingleton _ _), Subsingleton.elim _ _⟩
  have := Module.finite_of_finrank_eq_succ hA
  have : Nontrivial A := Module.nontrivial_of_finrank_eq_succ hA
  have : Module.Free R (A ⧸ R ∙ (1 : A)) := free_quotient_one_iff.1 ‹_›
  exact isUnimodular_one.exists_basis_zero_eq_of_free_quotient hA

end Free

end Module
