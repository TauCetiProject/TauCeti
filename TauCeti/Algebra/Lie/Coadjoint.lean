/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Lie.Prod
public import Mathlib.LinearAlgebra.Dual.Defs
public import Mathlib.LinearAlgebra.Quotient.Bilinear
public import TauCeti.Algebra.Lie.Basic
public import TauCeti.LinearAlgebra.Quotient.Prod

/-!
# The Kirillov–Kostant–Souriau form on a coadjoint tangent space

A Lie algebra `L` over a commutative ring `R` acts on its dual `L* = Module.Dual R L` by the
coadjoint action `⁅ξ, ν⁆ = -ν ∘ ad ξ` (Mathlib's `Module.Dual.instLieRingModule`). Fix `ν ∈ L*` and
let `L_ν = {ξ | ⁅ξ, ν⁆ = 0}` be its stabilizer (`TauCeti.lieAnnihilator R L ν`). Everything in this
file is linear algebra: the quotient `L ⧸ L_ν` is the **algebraic tangent model** of the coadjoint
orbit through `ν`, and the injective map `[ξ] ↦ ⁅ξ, ν⁆` from `L ⧸ L_ν` onto `L · ν ⊆ L*`
(`Module.Dual.coadjointTangentMap ν`) is its algebraic orbit derivative.

These names carry their geometric meaning only when `L` is the Lie algebra of a Lie group `G`
whose coadjoint orbit through `ν` is a smooth homogeneous space `G / G_ν` (for instance a real
finite-dimensional Lie group). In that case the coadjoint action is the derivative of
`ν ↦ ν ∘ Ad_(g⁻¹)`, the derivative at the identity of the orbit map `g ↦ g · ν` is `ξ ↦ ⁅ξ, ν⁆` on
`L` with kernel `L_ν`, the tangent space of the orbit at `ν` is `L ⧸ L_ν`, and
`coadjointTangentMap ν` is the map induced on this quotient: the derivative at the identity coset
of the map `G / G_ν → L*`, `[g] ↦ g · ν`.

The **Kirillov form** `B_ν(ξ, η) = ν ⁅ξ, η⁆` on `L` (`Module.Dual.kirillovForm ν`) is alternating,
and its kernel is exactly the stabilizer `L_ν` (`Module.Dual.ker_kirillovForm`). It therefore
descends to the **Kirillov–Kostant–Souriau form**

`ω_ν([ξ], [η]) = ν ⁅ξ, η⁆`

on `L ⧸ L_ν` (`Module.Dual.kksForm ν`), which is alternating and nondegenerate. This holds over an
arbitrary commutative ring and with no finiteness assumption, so the algebraic tangent model at
every `ν` carries a nondegenerate alternating bilinear form. With trivial coefficients the
Kirillov form is minus the Chevalley–Eilenberg coboundary of `ν` (compare Mathlib's
`LieModule.Cohomology.d₁₂`); it is stated directly here because `R` carries no trivial `L`-module
instance.

Two identities of `ω_ν` are, under the geometric hypotheses above, the pointwise content of the
facts that the coadjoint orbit is a Hamiltonian space with closed form:

* contraction of `ω_ν` with the generator `[ξ]` is evaluation at `ξ` after the orbit derivative
  (`Module.Dual.kksForm_mk_left`): this is the moment map equation `ι_(ξ_O) ω = d⟨ι, ξ⟩` at `ν`
  for the inclusion `ι` of the orbit into `L*`;
* the cyclic sum of `ω_ν([⁅ξ, η⁆], [ζ])` vanishes (`Module.Dual.kksForm_jacobi`), which is the
  Jacobi identity and gives closedness of the invariant form on the orbit.

The construction is natural. A surjective Lie algebra map `f : L → L'` with `ν = ν' ∘ f` pulls
the stabilizer back, `L_ν = f⁻¹(L'_ν')`, and induces the equivalence `[ξ] ↦ [f ξ]` of algebraic
tangent models carrying `ω_ν'` to `ω_ν` and intertwining the orbit derivatives through the dual map
`f^*`. This covers Lie algebra automorphisms, such as the adjoint maps of a Lie group, which act on
coadjoint orbits by symplectomorphisms, as well as the isomorphism of Lie algebras induced by a
covering homomorphism and quotients by central ideals. For a product `L₁ × L₂` and the functional
`(η₁, η₂) ↦ ν₁ η₁ + ν₂ η₂`, the stabilizer is the product of the stabilizers and the KKS form is
the sum of the two factor forms.

Finally, the positive Lie–Poisson tensor of `L*` at `ν`, `{ℓ_α, ℓ_β}(ν) = ν ⁅α, β⁆`, is the Kirillov
form on covectors `α, β ∈ L`, with sharp map `β(π♯α) = π(α, β)`. Its sharp image
`π♯α = -⁅α, ν⁆` is the orbit derivative of `[-α]`, and the KKS form evaluated on the preimages
of `π♯α` and `π♯β` is `π_ν(α, β)`. This fixes the signs relating the KKS form to the Lie–Poisson
structure.

## Main definitions

* `Module.Dual.kirillovForm ν`: the bilinear form `ν ⁅ξ, η⁆` on `L`.
* `Module.Dual.coadjointTangentMap ν`: the injection `[ξ] ↦ ⁅ξ, ν⁆` of `L ⧸ L_ν` into `L*`.
* `Module.Dual.kksForm ν`: the Kirillov–Kostant–Souriau form on `L ⧸ L_ν`.
* `Module.Dual.quotientLieAnnihilatorEquiv`: the equivalence `L ⧸ L_ν ≃ L' ⧸ L'_ν'` induced by a
  surjective Lie algebra map `f` with `ν = ν' ∘ f`.
* `Module.Dual.quotientLieAnnihilatorProdEquiv`: the equivalence of the tangent model of a product
  functional on `L₁ × L₂` with the product of the tangent models.

## Main results

* `Module.Dual.ker_kirillovForm`: the kernel of the Kirillov form is the stabilizer `L_ν`.
* `Module.Dual.coadjointTangentMap_injective`: the orbit derivative is injective.
* `Module.Dual.isAlt_kksForm`, `Module.Dual.kksForm_nondegenerate`: `ω_ν` is alternating and
  nondegenerate.
* `Module.Dual.lieAnnihilator_eq_comap`: stabilizers pull back along surjective Lie algebra maps.
* `Module.Dual.kksForm_quotientLieAnnihilatorEquiv`: naturality of the KKS form.
* `Module.Dual.toSubmodule_lieAnnihilator_coprod`, `Module.Dual.kksForm_coprod`: the stabilizer
  and the KKS form of a product functional.
* `Module.Dual.finrank_quotient_lieAnnihilator_coprod`: the dimensions of the tangent models add
  over products.
* `Module.Dual.kirillovForm_eq_coadjointTangentMap_mk_neg`: the Lie–Poisson sharp image `π♯α` is
  the orbit derivative of `[-α]`.
* `Module.Dual.kksForm_eq_kirillovForm_of_coadjointTangentMap_eq`: the KKS form inverts the
  Lie–Poisson sharp map.

## References

* A. A. Kirillov, *Lectures on the Orbit Method*, Graduate Studies in Mathematics 64, AMS, 2004,
  Section 1.2.
* A. Cannas da Silva, *Lectures on Symplectic Geometry*, Lecture Notes in Mathematics 1764,
  Springer, 2001, Section 22.
* Jerrold Marsden and Tudor Ratiu, *Introduction to Mechanics and Symmetry*, second edition,
  §§10.1 and 14.3 (the Lie–Poisson bracket and the coadjoint orbit symplectic structure).
-/

public section

open Module TauCeti

attribute [local instance 100] LieRing.ofAssociativeRing

namespace Module.Dual

variable {R L : Type*} [CommRing R] [LieRing L] [LieAlgebra R L] (ν : Dual R L)

/-- The **Kirillov form** `B_ν(ξ, η) = ν ⁅ξ, η⁆` of a linear functional `ν` on a Lie algebra. Its
kernel is the coadjoint stabilizer of `ν` (`Module.Dual.ker_kirillovForm`). -/
def kirillovForm : LinearMap.BilinForm R L :=
  (LieAlgebra.ad R L).toLinearMap.compr₂ ν

@[simp]
theorem kirillovForm_apply (ξ η : L) : ν.kirillovForm ξ η = ν ⁅ξ, η⁆ :=
  (rfl)

/-- The Kirillov form is alternating. -/
theorem isAlt_kirillovForm : ν.kirillovForm.IsAlt := fun ξ ↦ by
  rw [kirillovForm_apply, lie_self, map_zero]

/-- The Kirillov form of `ν` pairs `ξ` with `η` to `-⁅ξ, ν⁆ η`. -/
theorem kirillovForm_eq_neg_lie_apply (ξ η : L) : ν.kirillovForm ξ η = -(⁅ξ, ν⁆ : Dual R L) η := by
  rw [kirillovForm_apply, Dual.lie_apply, neg_neg]

/-- The kernel of the Kirillov form `ν ⁅ξ, η⁆` is the coadjoint stabilizer `L_ν` of `ν`. -/
theorem ker_kirillovForm :
    LinearMap.ker ν.kirillovForm = (lieAnnihilator R L ν).toSubmodule := by
  ext ξ
  simp only [LinearMap.mem_ker, LieSubalgebra.mem_toSubmodule, mem_lieAnnihilator,
    LinearMap.ext_iff, kirillovForm_eq_neg_lie_apply, LinearMap.zero_apply, neg_eq_zero]

/-- The algebraic orbit derivative `[ξ] ↦ ⁅ξ, ν⁆`, identifying the algebraic tangent model
`L ⧸ L_ν` with the subspace `L · ν = {⁅ξ, ν⁆}` of `L*`. When `L` integrates to a Lie group `G` whose
coadjoint orbit through `ν` is a smooth homogeneous space `G / G_ν`, this is the map induced on
`L ⧸ L_ν` by the derivative `ξ ↦ ⁅ξ, ν⁆` at the identity of the orbit map `g ↦ Ad*_g ν`, that is,
the derivative at the identity coset of the map `G / G_ν → L*`, `[g] ↦ Ad*_g ν`. -/
def coadjointTangentMap : (L ⧸ (lieAnnihilator R L ν).toSubmodule) →ₗ[R] Dual R L :=
  (lieAnnihilator R L ν).toSubmodule.liftQ
    ((LieModule.toEnd R L (Dual R L)).toLinearMap.flip ν)
    fun _ hξ ↦ (mem_lieAnnihilator R L).mp hξ

@[simp]
theorem coadjointTangentMap_mk (ξ : L) :
    ν.coadjointTangentMap (Submodule.Quotient.mk ξ) = ⁅ξ, ν⁆ :=
  (rfl)

/-- The orbit derivative `[ξ] ↦ ⁅ξ, ν⁆` is injective: the map `ξ ↦ ⁅ξ, ν⁆` on `L` has kernel the
stabilizer `L_ν`, so the induced map on `L ⧸ L_ν` is injective. -/
theorem coadjointTangentMap_injective : Function.Injective ν.coadjointTangentMap :=
  LinearMap.ker_eq_bot.mp <| Submodule.ker_liftQ_eq_bot _ _ _
    fun _ hξ ↦ (mem_lieAnnihilator R L).mpr hξ

/-- The **Kirillov–Kostant–Souriau form** on the algebraic tangent model `L ⧸ L_ν` of the coadjoint
orbit through `ν`, the descent of the Kirillov form: `ω_ν([ξ], [η]) = ν ⁅ξ, η⁆`
(`Module.Dual.kksForm_mk`). -/
def kksForm : LinearMap.BilinForm R (L ⧸ (lieAnnihilator R L ν).toSubmodule) :=
  ν.isAlt_kirillovForm.isRefl.liftQ₂ ν.kirillovForm _ ν.ker_kirillovForm.ge

/-- The defining formula `ω_ν([ξ], [η]) = ν ⁅ξ, η⁆` of the Kirillov–Kostant–Souriau form. -/
@[simp]
theorem kksForm_mk (ξ η : L) :
    ν.kksForm (Submodule.Quotient.mk ξ) (Submodule.Quotient.mk η) = ν ⁅ξ, η⁆ :=
  (rfl)

/-- Contracting the Kirillov–Kostant–Souriau form with the generator `[ξ]` is evaluation at `ξ`
after the algebraic orbit derivative. When the coadjoint orbit through `ν` is a smooth homogeneous
space of a Lie group integrating `L`, this is the moment map equation `ι_(ξ_O) ω = d⟨ι, ξ⟩` at `ν`
for the inclusion `ι` of the orbit into `L*`, whose derivative is `coadjointTangentMap ν`. -/
theorem kksForm_mk_left (ξ : L) (y : L ⧸ (lieAnnihilator R L ν).toSubmodule) :
    ν.kksForm (Submodule.Quotient.mk ξ) y = ν.coadjointTangentMap y ξ := by
  induction y using Submodule.Quotient.induction_on with
  | H η => rw [kksForm_mk, coadjointTangentMap_mk, Dual.lie_apply, ← lie_skew, map_neg]

/-- The Kirillov–Kostant–Souriau form is alternating. -/
theorem isAlt_kksForm : ν.kksForm.IsAlt := by
  intro x
  induction x using Submodule.Quotient.induction_on with
  | H ξ => rw [kksForm_mk, ← kirillovForm_apply]; exact ν.isAlt_kirillovForm ξ

/-- The Kirillov–Kostant–Souriau form is nondegenerate, over any commutative ring and in any
dimension: if `ν ⁅ξ, η⁆ = 0` for every `η`, then `ξ` stabilizes `ν`. -/
theorem kksForm_nondegenerate : ν.kksForm.Nondegenerate := by
  refine (LinearMap.IsRefl.nondegenerate_iff_separatingLeft ν.isAlt_kksForm.isRefl).mpr ?_
  intro x hx
  induction x using Submodule.Quotient.induction_on with
  | H ξ =>
    rw [Submodule.Quotient.mk_eq_zero, ← ker_kirillovForm, LinearMap.mem_ker]
    ext η
    rw [kirillovForm_apply, LinearMap.zero_apply, ← kksForm_mk]
    exact hx (Submodule.Quotient.mk η)

/-- The cyclic sum of the Kirillov–Kostant–Souriau form on brackets of generators vanishes. This
is the Jacobi identity, and it is the algebraic input to closedness of the invariant form on the
coadjoint orbit when that orbit is a smooth homogeneous space. -/
theorem kksForm_jacobi (ξ η ζ : L) :
    ν.kksForm (Submodule.Quotient.mk ⁅ξ, η⁆) (Submodule.Quotient.mk ζ) +
      ν.kksForm (Submodule.Quotient.mk ⁅η, ζ⁆) (Submodule.Quotient.mk ξ) +
        ν.kksForm (Submodule.Quotient.mk ⁅ζ, ξ⁆) (Submodule.Quotient.mk η) = 0 := by
  have skew (a b c : L) : ν ⁅⁅a, b⁆, c⁆ = -ν ⁅c, ⁅a, b⁆⁆ := by
    rw [← lie_skew ⁅a, b⁆ c, map_neg]
  simp only [kksForm_mk, skew]
  convert congrArg (fun x : L => -ν x) (lie_jacobi ξ η ζ) using 1 <;>
    simp only [map_add, map_zero, neg_zero]
  abel

/-! ### Naturality under surjective Lie algebra maps -/

section Map

variable {L' : Type*} [LieRing L'] [LieAlgebra R L'] {ν} (ν' : Dual R L') {f : L →ₗ⁅R⁆ L'}

/-- Along a Lie algebra map `f : L → L'` with `ν = ν' ∘ f`, the dual map `f^*` intertwines the
coadjoint actions: `f^* ⁅f ξ, ν'⁆ = ⁅ξ, ν⁆`. -/
theorem lie_comp_of_comp_eq (hν : ν'.comp (f : L →ₗ[R] L') = ν) (ξ : L) :
    (⁅f ξ, ν'⁆ : Dual R L').comp (f : L →ₗ[R] L') = ⁅ξ, ν⁆ := by
  subst hν
  ext η
  simp

/-- Along a Lie algebra map `f : L → L'` with `ν = ν' ∘ f`, the Kirillov form of `ν` is the
pullback of that of `ν'`. -/
theorem kirillovForm_eq_of_comp_eq (hν : ν'.comp (f : L →ₗ[R] L') = ν) (ξ η : L) :
    ν.kirillovForm ξ η = ν'.kirillovForm (f ξ) (f η) := by
  subst hν
  simp

variable {ν'}

/-- **Coadjoint stabilizers pull back along surjective Lie algebra maps.** If `f : L → L'` is a
surjective Lie algebra map and `ν = ν' ∘ f`, then `L_ν = f⁻¹(L'_ν')`. In particular `L_ν` contains
the kernel of `f`. -/
theorem lieAnnihilator_eq_comap (hf : Function.Surjective f)
    (hν : ν'.comp (f : L →ₗ[R] L') = ν) :
    lieAnnihilator R L ν = (lieAnnihilator R L' ν').comap f := by
  ext ξ
  rw [LieSubalgebra.mem_comap, mem_lieAnnihilator, mem_lieAnnihilator,
    ← lie_comp_of_comp_eq ν' hν]
  refine ⟨fun h ↦ ?_, fun h ↦ by rw [h, LinearMap.zero_comp]⟩
  ext η'
  obtain ⟨η, rfl⟩ := hf η'
  simpa using LinearMap.congr_fun h η

/-- The submodule form of `Module.Dual.lieAnnihilator_eq_comap`, the hypothesis of
`Submodule.mapQ`. -/
private theorem toSubmodule_lieAnnihilator_eq_comap (hf : Function.Surjective f)
    (hν : ν'.comp (f : L →ₗ[R] L') = ν) :
    (lieAnnihilator R L ν).toSubmodule =
      (lieAnnihilator R L' ν').toSubmodule.comap (f : L →ₗ[R] L') := by
  ext ξ
  rw [LieSubalgebra.mem_toSubmodule, lieAnnihilator_eq_comap hf hν, LieSubalgebra.mem_comap,
    Submodule.mem_comap, LieSubalgebra.mem_toSubmodule, LieHom.coe_toLinearMap]

variable (ν')

/-- A surjective Lie algebra map `f : L → L'` with `ν = ν' ∘ f` induces the linear equivalence
`[ξ] ↦ [f ξ]` (`Module.Dual.quotientLieAnnihilatorEquiv_mk`) from the algebraic tangent model
`L ⧸ L_ν` of the coadjoint orbit through `ν` onto that of `ν'`. It carries the
Kirillov–Kostant–Souriau form of `ν'` back to that of `ν`
(`Module.Dual.kksForm_quotientLieAnnihilatorEquiv`). For a Lie algebra automorphism this is the
invariance of the KKS form; for the differential of a covering homomorphism of Lie groups it
identifies the coadjoint orbit models of the two groups. -/
noncomputable def quotientLieAnnihilatorEquiv (hf : Function.Surjective f)
    (hν : ν'.comp (f : L →ₗ[R] L') = ν) :
    (L ⧸ (lieAnnihilator R L ν).toSubmodule) ≃ₗ[R] L' ⧸ (lieAnnihilator R L' ν').toSubmodule :=
  LinearEquiv.ofBijective
    ((lieAnnihilator R L ν).toSubmodule.mapQ _ (f : L →ₗ[R] L')
      (toSubmodule_lieAnnihilator_eq_comap hf hν).le)
    ⟨LinearMap.ker_eq_bot.mp <| by
        rw [Submodule.ker_mapQ, ← toSubmodule_lieAnnihilator_eq_comap hf hν,
          Submodule.mkQ_map_self],
      fun y ↦ by
        induction y using Submodule.Quotient.induction_on with
        | H η' =>
          obtain ⟨η, rfl⟩ := hf η'
          exact ⟨Submodule.Quotient.mk η, rfl⟩⟩

variable (hf : Function.Surjective f) (hν : ν'.comp (f : L →ₗ[R] L') = ν)

@[simp]
theorem quotientLieAnnihilatorEquiv_mk (ξ : L) :
    quotientLieAnnihilatorEquiv ν' hf hν (Submodule.Quotient.mk ξ) =
      Submodule.Quotient.mk (f ξ) :=
  (rfl)

@[simp]
theorem quotientLieAnnihilatorEquiv_symm_mk (ξ : L) :
    (quotientLieAnnihilatorEquiv ν' hf hν).symm (Submodule.Quotient.mk (f ξ)) =
      Submodule.Quotient.mk ξ := by
  rw [LinearEquiv.symm_apply_eq, quotientLieAnnihilatorEquiv_mk]

/-- **Naturality of the Kirillov–Kostant–Souriau form.** Along a surjective Lie algebra map
`f : L → L'` with `ν = ν' ∘ f`, the equivalence `[ξ] ↦ [f ξ]` of algebraic tangent models carries
`ω_ν'` to `ω_ν`. -/
@[simp]
theorem kksForm_quotientLieAnnihilatorEquiv (x y : L ⧸ (lieAnnihilator R L ν).toSubmodule) :
    ν'.kksForm (quotientLieAnnihilatorEquiv ν' hf hν x)
        (quotientLieAnnihilatorEquiv ν' hf hν y) = ν.kksForm x y := by
  induction x using Submodule.Quotient.induction_on with
  | H ξ =>
    induction y using Submodule.Quotient.induction_on with
    | H η =>
      rw [quotientLieAnnihilatorEquiv_mk, quotientLieAnnihilatorEquiv_mk, kksForm_mk, kksForm_mk,
        ← kirillovForm_apply, ← kirillovForm_apply, kirillovForm_eq_of_comp_eq ν' hν]

/-- Along a surjective Lie algebra map `f : L → L'` with `ν = ν' ∘ f`, the orbit derivatives
correspond under the dual map `f^*`: `f^* (T_ν' [f ξ]) = T_ν [ξ]`. -/
@[simp]
theorem coadjointTangentMap_quotientLieAnnihilatorEquiv
    (x : L ⧸ (lieAnnihilator R L ν).toSubmodule) :
    (ν'.coadjointTangentMap (quotientLieAnnihilatorEquiv ν' hf hν x)).comp (f : L →ₗ[R] L') =
      ν.coadjointTangentMap x := by
  induction x using Submodule.Quotient.induction_on with
  | H ξ =>
    rw [quotientLieAnnihilatorEquiv_mk, coadjointTangentMap_mk, coadjointTangentMap_mk,
      lie_comp_of_comp_eq ν' hν]

end Map

/-! ### Products -/

section Prod

variable {L₁ L₂ : Type*} [LieRing L₁] [LieAlgebra R L₁] [LieRing L₂] [LieAlgebra R L₂]
  (ν₁ : Dual R L₁) (ν₂ : Dual R L₂)

/-- The coadjoint action of `L₁ × L₂` on the functional `(η₁, η₂) ↦ ν₁ η₁ + ν₂ η₂` is
componentwise. -/
@[simp]
theorem lie_coprod (ξ : L₁ × L₂) :
    ⁅ξ, (ν₁.coprod ν₂ : Dual R (L₁ × L₂))⁆ = (⁅ξ.1, ν₁⁆ : Dual R L₁).coprod ⁅ξ.2, ν₂⁆ := by
  ext <;> simp

/-- **The coadjoint stabilizer of a product functional is the product of the stabilizers.** -/
theorem toSubmodule_lieAnnihilator_coprod :
    (lieAnnihilator R (L₁ × L₂) (ν₁.coprod ν₂)).toSubmodule =
      (lieAnnihilator R L₁ ν₁).toSubmodule.prod (lieAnnihilator R L₂ ν₂).toSubmodule := by
  ext ξ
  simp only [LieSubalgebra.mem_toSubmodule, mem_lieAnnihilator, Submodule.mem_prod, lie_coprod]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun h ↦ by rw [h.1, h.2, LinearMap.coprod_zero_left,
    LinearMap.zero_comp]⟩
  · simpa using congrArg (fun g ↦ g.comp (LinearMap.inl R L₁ L₂)) h
  · simpa using congrArg (fun g ↦ g.comp (LinearMap.inr R L₁ L₂)) h

/-- The algebraic tangent model of the coadjoint orbit of `(η₁, η₂) ↦ ν₁ η₁ + ν₂ η₂` in the
product Lie algebra `L₁ × L₂` is the product of those of `ν₁` and `ν₂`, by
`[(ξ₁, ξ₂)] ↦ ([ξ₁], [ξ₂])` (`Module.Dual.quotientLieAnnihilatorProdEquiv_mk`). It carries the
Kirillov–Kostant–Souriau form to the sum of the two factor forms
(`Module.Dual.kksForm_coprod`). -/
noncomputable def quotientLieAnnihilatorProdEquiv :
    ((L₁ × L₂) ⧸ (lieAnnihilator R (L₁ × L₂) (ν₁.coprod ν₂)).toSubmodule) ≃ₗ[R]
      (L₁ ⧸ (lieAnnihilator R L₁ ν₁).toSubmodule) × (L₂ ⧸ (lieAnnihilator R L₂ ν₂).toSubmodule) :=
  (Submodule.quotEquivOfEq _ _ (toSubmodule_lieAnnihilator_coprod ν₁ ν₂)).trans
    (Submodule.quotientProdEquiv _ _)

@[simp]
theorem quotientLieAnnihilatorProdEquiv_mk (ξ : L₁ × L₂) :
    ν₁.quotientLieAnnihilatorProdEquiv ν₂ (Submodule.Quotient.mk ξ) =
      (Submodule.Quotient.mk ξ.1, Submodule.Quotient.mk ξ.2) := by
  simp [quotientLieAnnihilatorProdEquiv]

@[simp]
theorem quotientLieAnnihilatorProdEquiv_symm_mk (ξ₁ : L₁) (ξ₂ : L₂) :
    (ν₁.quotientLieAnnihilatorProdEquiv ν₂).symm
        (Submodule.Quotient.mk ξ₁, Submodule.Quotient.mk ξ₂) =
      Submodule.Quotient.mk (ξ₁, ξ₂) := by
  rw [LinearEquiv.symm_apply_eq, quotientLieAnnihilatorProdEquiv_mk]

/-- **The Kirillov–Kostant–Souriau form of a product is the sum of the factor forms.** Under
`[(ξ₁, ξ₂)] ↦ ([ξ₁], [ξ₂])`, the KKS form of `(η₁, η₂) ↦ ν₁ η₁ + ν₂ η₂` on `L₁ × L₂` is
`ω_ν₁ + ω_ν₂`. -/
theorem kksForm_coprod
    (x y : (L₁ × L₂) ⧸ (lieAnnihilator R (L₁ × L₂) (ν₁.coprod ν₂)).toSubmodule) :
    kksForm (ν₁.coprod ν₂) x y =
      ν₁.kksForm (ν₁.quotientLieAnnihilatorProdEquiv ν₂ x).1
          (ν₁.quotientLieAnnihilatorProdEquiv ν₂ y).1 +
        ν₂.kksForm (ν₁.quotientLieAnnihilatorProdEquiv ν₂ x).2
          (ν₁.quotientLieAnnihilatorProdEquiv ν₂ y).2 := by
  induction x using Submodule.Quotient.induction_on with
  | H ξ =>
    induction y using Submodule.Quotient.induction_on with
    | H η => simp

/-- **Coadjoint orbit dimensions add over products.** When the algebraic tangent models of `ν₁` and
`ν₂` are free of finite rank, that of `(η₁, η₂) ↦ ν₁ η₁ + ν₂ η₂` in `L₁ × L₂` has rank
`rank (L₁ ⧸ L₁_ν₁) + rank (L₂ ⧸ L₂_ν₂)`. -/
theorem finrank_quotient_lieAnnihilator_coprod [StrongRankCondition R]
    [Module.Free R (L₁ ⧸ (lieAnnihilator R L₁ ν₁).toSubmodule)]
    [Module.Free R (L₂ ⧸ (lieAnnihilator R L₂ ν₂).toSubmodule)]
    [Module.Finite R (L₁ ⧸ (lieAnnihilator R L₁ ν₁).toSubmodule)]
    [Module.Finite R (L₂ ⧸ (lieAnnihilator R L₂ ν₂).toSubmodule)] :
    finrank R ((L₁ × L₂) ⧸ (lieAnnihilator R (L₁ × L₂) (ν₁.coprod ν₂)).toSubmodule) =
      finrank R (L₁ ⧸ (lieAnnihilator R L₁ ν₁).toSubmodule) +
        finrank R (L₂ ⧸ (lieAnnihilator R L₂ ν₂).toSubmodule) := by
  rw [toSubmodule_lieAnnihilator_coprod, Submodule.finrank_quotient_prod]

end Prod

/-! ### The Lie–Poisson sharp map -/

/-- The Lie–Poisson sharp image `π♯α = ν.kirillovForm α = -⁅α, ν⁆` is the orbit derivative of
`[-α] ∈ L ⧸ L_ν`. -/
theorem kirillovForm_eq_coadjointTangentMap_mk_neg (α : L) :
    ν.kirillovForm α = ν.coadjointTangentMap (Submodule.Quotient.mk (-α)) := by
  ext η
  rw [kirillovForm_eq_neg_lie_apply, coadjointTangentMap_mk, neg_lie, LinearMap.neg_apply]

/-- **The Kirillov–Kostant–Souriau form inverts the Lie–Poisson sharp map.** The positive
Lie–Poisson tensor of `L*` at `ν`, `{ℓ_α, ℓ_β}(ν) = ν ⁅α, β⁆`, is the Kirillov form on covectors
`α, β ∈ L ⊆ L**`, and its sharp map `β(π♯α) = π(α, β)` is `α ↦ ν.kirillovForm α`. If the orbit
derivative carries `x, y ∈ L ⧸ L_ν` to `π♯α` and `π♯β`, then `ω_ν(x, y) = π_ν(α, β)`. -/
theorem kksForm_eq_kirillovForm_of_coadjointTangentMap_eq {α β : L}
    {x y : L ⧸ (lieAnnihilator R L ν).toSubmodule}
    (hx : ν.coadjointTangentMap x = ν.kirillovForm α)
    (hy : ν.coadjointTangentMap y = ν.kirillovForm β) :
    ν.kksForm x y = ν.kirillovForm α β := by
  rw [kirillovForm_eq_coadjointTangentMap_mk_neg] at hx hy
  rw [ν.coadjointTangentMap_injective hx, ν.coadjointTangentMap_injective hy, kksForm_mk,
    kirillovForm_apply, neg_lie, lie_neg, neg_neg]

end Module.Dual
