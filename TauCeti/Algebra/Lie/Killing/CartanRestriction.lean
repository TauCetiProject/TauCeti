/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.Killing.SymmetricAlgebra
public import TauCeti.Algebra.Lie.Weights.Borel
public import TauCeti.Algebra.Lie.Weights.InvariantForm
public import TauCeti.Algebra.Lie.Weights.Projection
public import TauCeti.LinearAlgebra.SymmetricAlgebra.Homogeneous
import TauCeti.LinearAlgebra.SymmetricAlgebra.Semilinear

/-!
# Restricting polynomial functions on a Killing Lie algebra to a Cartan subalgebra

Let `L` be a finite-dimensional Lie algebra over a field `K` whose Killing form `κ` is
nondegenerate, and `H` a Cartan subalgebra. The Killing form stays nondegenerate on `H`, so every
`x : L` has a unique **Killing-orthogonal projection** `π x ∈ H`, characterized by
`κ(π x, h) = κ(x, h)` for all `h ∈ H`. It is the identity on `H` and, when `H` splits `L`,
vanishes on every root space of a nonzero root, so it is the projection of `L` onto `H` along the
sum of the nonzero root spaces (`TauCeti.coe_killingCartanProjection`).

Through the Killing identifications `S(L) ≃ S(L*)` (`TauCeti.killingSymmetricEquiv`) and
`S(H) ≃ S(H*)` (induced by `LieAlgebra.IsKilling.cartanEquivDual`), the symmetric algebras `S(L)`
and `S(H)` are the algebras of polynomial functions on `L` and on `H`. Restriction of polynomial
functions from `L` to `H` is then the algebra map `S(L) → S(H)` induced by `π`,

`TauCeti.lieCartanRestriction H : S(L) →ₐ[K] S(H)`.

This is the map that Chevalley's restriction theorem is about: restricted to the invariants
`S(L)^L`, it is an isomorphism onto the Weyl invariants `S(H)^W`
(`LieSubalgebra.lieChevalleyRestrictionIso`), and through the PBW symbols of central elements it
is compared with the Harish-Chandra projection.

Read on the dual side, with `S(L)` as the polynomial functions on `L*` and `S(H)` as the polynomial
functions on the weights `H*`, the restriction evaluates a polynomial on `L*` at the extension
`TauCeti.killingExtend λ = λ ∘ π` of a weight `λ` to `L` (`TauCeti.lift_lieCartanRestriction`).

## Main definitions

* `TauCeti.killingCartanProjection H`: the Killing-orthogonal projection `L →ₗ[K] H`.
* `TauCeti.lieCartanRestriction H`: the induced algebra map `S(L) →ₐ[K] S(H)`.

## Main results

* `TauCeti.killingForm_killingCartanProjection`: `κ(π x, h) = κ(x, h)` for `h ∈ H`.
* `TauCeti.killingCartanProjection_coe` and
  `TauCeti.killingCartanProjection_eq_zero_of_mem_rootSpace`: the projection is the identity on `H`
  and vanishes on the root spaces of nonzero roots.
* `TauCeti.killingCartanProjection_eq_zero_of_mem_negativeNilradical` and
  `TauCeti.killingCartanProjection_eq_zero_of_mem_positiveNilradical`: for a base `b` of the root
  system, the projection vanishes on both nilradicals.
* `TauCeti.lieCartanRestriction_ι_cartan` and `TauCeti.lieCartanRestriction_ι_root`: the same for
  the restriction map on generators.
* `TauCeti.coe_killingCartanProjection`: the projection is the projection
  `TauCeti.genWeightSpaceProjection` of the root-space decomposition at the zero weight.
* `TauCeti.killingExtend_eq_comp_killingCartanProjection`: the extension `TauCeti.killingExtend λ`
  of a weight to `L` is `λ ∘ π`.
* `TauCeti.map_dualMap_killingSymmetricEquiv`: **the restriction square.** Restricting a polynomial
  function on `L` to `H` along the inclusion commutes with the Killing identifications, the
  restriction on the `S(L)` side being `lieCartanRestriction H`.
* `TauCeti.lift_lieCartanRestriction`: the value of `lieCartanRestriction H p` at a weight `λ` is
  the value of `p` at `TauCeti.killingExtend λ`.
* `TauCeti.lieCartanRestriction_mem_homogeneousSubmodule`: the restriction preserves degrees.
* `TauCeti.lieCartanRestriction_surjective`: the restriction is onto, split by the map induced by
  the inclusion `H → L`.

## References

* J. E. Humphreys, *Introduction to Lie Algebras and Representation Theory*, GTM 9, §23.1, for the
  restriction of polynomial functions to `H` and Chevalley's restriction theorem.
* J. Dixmier, *Enveloping Algebras*, §7.3.
-/

public section

namespace TauCeti

open LieAlgebra LieAlgebra.IsKilling _root_.LieModule Module

variable {K L : Type*} [Field K] [LieRing L] [LieAlgebra K L] [FiniteDimensional K L]
  [IsKilling K L] (H : LieSubalgebra K L) [H.IsCartanSubalgebra]

/-! ### The Killing-orthogonal projection onto a Cartan subalgebra -/

/-- **The Killing-orthogonal projection** `π : L → H` onto a Cartan subalgebra: `π x` is the
element of `H` representing the linear form `h ↦ κ(x, h)` on `H` under the restricted Killing form
(`TauCeti.killingForm_killingCartanProjection`). It is the identity on `H`
(`TauCeti.killingCartanProjection_coe`) and kills the root spaces of nonzero roots
(`TauCeti.killingCartanProjection_eq_zero_of_mem_rootSpace`). -/
noncomputable def killingCartanProjection : L →ₗ[K] H :=
  (cartanEquivDual H).symm.toLinearMap ∘ₗ H.incl.toLinearMap.dualMap ∘ₗ killingForm K L

/-- The projection `π x` represents the restriction of `κ(x, ·)` to `H` under
`LieAlgebra.IsKilling.cartanEquivDual`. -/
theorem cartanEquivDual_killingCartanProjection (x : L) :
    cartanEquivDual H (killingCartanProjection H x) =
      H.incl.toLinearMap.dualMap (killingForm K L x) :=
  (cartanEquivDual H).apply_symm_apply _

/-- **The characteristic property of the projection**: `κ(π x, h) = κ(x, h)` for every `h ∈ H`. -/
@[simp]
theorem killingForm_killingCartanProjection (x : L) (h : H) :
    killingForm K L (killingCartanProjection H x) h = killingForm K L x h := by
  rw [← cartanEquivDual_apply_apply_eq_killingForm, cartanEquivDual_killingCartanProjection,
    LinearMap.dualMap_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl]

/-- The projection `π x` is the only element of `H` whose Killing pairings with `H` are those of
`x`. -/
theorem eq_killingCartanProjection_iff {x : L} {y : H} :
    y = killingCartanProjection H x ↔ ∀ h : H, killingForm K L y h = killingForm K L x h := by
  refine ⟨fun hy h ↦ hy ▸ killingForm_killingCartanProjection H x h, fun hy ↦ ?_⟩
  refine (cartanEquivDual H).injective (LinearMap.ext fun h ↦ ?_)
  rw [cartanEquivDual_killingCartanProjection, cartanEquivDual_apply_apply_eq_killingForm, hy,
    LinearMap.dualMap_apply, LieHom.coe_toLinearMap, LieSubalgebra.coe_incl]

/-- The projection is the identity on `H`. -/
@[simp]
theorem killingCartanProjection_coe (h : H) : killingCartanProjection H (h : L) = h :=
  ((eq_killingCartanProjection_iff H).mpr fun _ ↦ rfl).symm

/-- The projection is a retraction of the inclusion `H → L`. -/
@[simp]
theorem killingCartanProjection_comp_incl :
    killingCartanProjection H ∘ₗ H.incl.toLinearMap = LinearMap.id :=
  LinearMap.ext (killingCartanProjection_coe H)

/-- The projection is onto. -/
theorem killingCartanProjection_surjective : Function.Surjective (killingCartanProjection H) :=
  fun h ↦ ⟨h, killingCartanProjection_coe H h⟩

/-- **The extension of a weight factors through the projection**: `TauCeti.killingExtend λ`, the
weight `λ` extended to `L` by pairing with the vector representing it, is `λ ∘ π`. -/
theorem killingExtend_eq_comp_killingCartanProjection (lam : Dual K H) :
    killingExtend lam = lam ∘ₗ killingCartanProjection H := by
  ext x
  rw [LinearMap.comp_apply, ← killingExtend_apply_cartan, killingExtend_apply, killingExtend_apply,
    traceForm_comm K L L _ (killingCartanProjection H x : L), killingForm_killingCartanProjection,
    traceForm_comm]

variable {H} in
/-- **The projection vanishes on the nonzero root spaces**: a vector in the root space of a nonzero
`χ` is Killing-orthogonal to `H`, the root space of `0`. -/
theorem killingCartanProjection_eq_zero_of_mem_rootSpace [IsTriangularizable K H L] {χ : H → K}
    (hχ : χ ≠ 0) {x : L} (hx : x ∈ rootSpace H χ) : killingCartanProjection H x = 0 := by
  refine ((eq_killingCartanProjection_iff H).mpr fun h ↦ ?_).symm
  rw [ZeroMemClass.coe_zero, map_zero, LinearMap.zero_apply]
  refine (killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H (β := 0) hx ?_
    (by rwa [add_zero])).symm
  rw [rootSpace_zero_eq K L H]
  exact h.2

variable {H} in
/-- **The projection is the root-space projection at the zero weight**: when `H` splits `L`, `π` is
the projection of `L` onto its zero root space `H` along the root spaces of the nonzero roots. -/
theorem coe_killingCartanProjection [IsTriangularizable K H L] [Nontrivial H] (x : L) :
    (killingCartanProjection H x : L) = genWeightSpaceProjection K H L 0 x := by
  have hmem : genWeightSpaceProjection K H L 0 x ∈ H := by
    simpa [rootSpace_zero_eq K L H] using genWeightSpaceProjection_apply_mem (0 : Weight K H L) x
  suffices ⟨_, hmem⟩ = killingCartanProjection H x from congrArg Subtype.val this.symm
  refine (eq_killingCartanProjection_iff H).mpr fun h ↦ ?_
  rw [killingForm_genWeightSpaceProjection, genWeightSpaceProjection_apply_of_mem]
  simp

/-! ### The projection on the nilradicals -/

section Nilradical

variable [CharZero K] [IsTriangularizable K H L]

variable {H} in
/-- The Killing-orthogonal projection onto `H` vanishes on the span of any set of root spaces. -/
theorem killingCartanProjection_eq_zero_of_mem_rootSpaceSpan {S : Set H.root} {x : L}
    (hx : x ∈ rootSpaceSpan H S) : killingCartanProjection H x = 0 := by
  have hle : (rootSpaceSpan H S : Submodule K L) ≤ LinearMap.ker (killingCartanProjection H) := by
    rw [rootSpaceSpan_eq_iSup, LieSubmodule.iSup_toSubmodule]
    exact iSup_le fun α _ hy ↦ killingCartanProjection_eq_zero_of_mem_rootSpace
      (Finset.mem_filter.mp (α : H.root).2).2 hy
  exact hle hx

variable {H} (b : (IsKilling.rootSystem H).Base)

/-- The Killing-orthogonal projection onto `H` vanishes on the negative nilradical. -/
theorem killingCartanProjection_eq_zero_of_mem_negativeNilradical {x : L}
    (hx : x ∈ negativeNilradical H b) : killingCartanProjection H x = 0 :=
  killingCartanProjection_eq_zero_of_mem_rootSpaceSpan ((mem_negativeNilradical H b x).mp hx)

/-- The Killing-orthogonal projection onto `H` vanishes on the positive nilradical. -/
theorem killingCartanProjection_eq_zero_of_mem_positiveNilradical {x : L}
    (hx : x ∈ positiveNilradical H b) : killingCartanProjection H x = 0 :=
  killingCartanProjection_eq_zero_of_mem_rootSpaceSpan ((mem_positiveNilradical H b x).mp hx)

end Nilradical

/-! ### Restriction of polynomial functions -/

/-- **Restriction of polynomial functions from `L` to `H`**: the algebra map `S(L) → S(H)` induced
by the Killing-orthogonal projection `π : L → H`. Under the Killing identifications of `S(L)` and
`S(H)` with the polynomial functions on `L` and on `H`, it is restriction along `H → L`
(`TauCeti.map_dualMap_killingSymmetricEquiv`). -/
noncomputable def lieCartanRestriction : SymmetricAlgebra K L →ₐ[K] SymmetricAlgebra K H :=
  SymmetricAlgebra.map K (killingCartanProjection H)

/-- The restriction sends the generator `x` to the generator `π x`. -/
@[simp]
theorem lieCartanRestriction_ι (x : L) :
    lieCartanRestriction H (SymmetricAlgebra.ι K L x) =
      SymmetricAlgebra.ι K H (killingCartanProjection H x) :=
  SymmetricAlgebra.map_apply_ι K _ x

/-- The restriction is the identity on the generators from `H`. -/
theorem lieCartanRestriction_ι_cartan (h : H) :
    lieCartanRestriction H (SymmetricAlgebra.ι K L h) = SymmetricAlgebra.ι K H h := by
  simp

variable {H} in
/-- The restriction kills the generators from the root spaces of nonzero roots. -/
theorem lieCartanRestriction_ι_root [IsTriangularizable K H L] {χ : H → K} (hχ : χ ≠ 0) {x : L}
    (hx : x ∈ rootSpace H χ) : lieCartanRestriction H (SymmetricAlgebra.ι K L x) = 0 := by
  rw [lieCartanRestriction_ι, killingCartanProjection_eq_zero_of_mem_rootSpace hχ hx, map_zero]

/-- The restriction is a retraction of the algebra map `S(H) → S(L)` induced by the inclusion. -/
@[simp]
theorem lieCartanRestriction_comp_map_incl :
    (lieCartanRestriction H).comp (SymmetricAlgebra.map K H.incl.toLinearMap) = AlgHom.id K _ := by
  rw [lieCartanRestriction, SymmetricAlgebra.map_comp_map, killingCartanProjection_comp_incl,
    SymmetricAlgebra.map_id]

/-- The restriction is onto. -/
theorem lieCartanRestriction_surjective : Function.Surjective (lieCartanRestriction H) :=
  SymmetricAlgebra.map_surjective_of_rightInverse K _ H.incl.toLinearMap
    (killingCartanProjection_coe H)

/-- The restriction preserves degrees: it maps the homogeneous component of degree `n` of `S(L)`
into that of `S(H)`. -/
theorem lieCartanRestriction_mem_homogeneousSubmodule {n : ℕ} {p : SymmetricAlgebra K L}
    (hp : p ∈ SymmetricAlgebra.homogeneousSubmodule K L n) :
    lieCartanRestriction H p ∈ SymmetricAlgebra.homogeneousSubmodule K H n :=
  SymmetricAlgebra.map_mem_homogeneousSubmodule _ hp

/-- **The restriction square.** Restricting a polynomial function on `L`, an element of
`S(L*)`, along the inclusion `H → L` commutes with the Killing identifications: transporting
`p ∈ S(L)` to `S(L*)` and restricting to `H` is the same as restricting `p` to `S(H)` by
`TauCeti.lieCartanRestriction` and transporting along `LieAlgebra.IsKilling.cartanEquivDual`. -/
theorem map_dualMap_killingSymmetricEquiv (p : SymmetricAlgebra K L) :
    SymmetricAlgebra.map K H.incl.toLinearMap.dualMap (killingSymmetricEquiv K L p) =
      SymmetricAlgebra.map K (cartanEquivDual H).toLinearMap (lieCartanRestriction H p) := by
  rw [killingSymmetricEquiv_apply, ← AlgHom.comp_apply, ← AlgHom.comp_apply, lieCartanRestriction,
    SymmetricAlgebra.map_comp_map, SymmetricAlgebra.map_comp_map]
  congr 2
  exact LinearMap.ext fun x ↦ (cartanEquivDual_killingCartanProjection H x).symm

/-- **The restriction, read on the weights.** Viewing `S(L)` as the polynomial functions on `L*`
and `S(H)` as the polynomial functions on the weights `H*`, the value of `lieCartanRestriction H p`
at a weight `λ` is the value of `p` at the extension `TauCeti.killingExtend λ` of `λ` to `L`. -/
@[simp]
theorem lift_lieCartanRestriction (lam : Dual K H) (p : SymmetricAlgebra K L) :
    SymmetricAlgebra.lift lam (lieCartanRestriction H p) =
      SymmetricAlgebra.lift (killingExtend lam) p := by
  rw [← AlgHom.comp_apply]
  congr 1
  refine SymmetricAlgebra.algHom_ext (LinearMap.ext fun x ↦ ?_)
  simp [killingExtend_eq_comp_killingCartanProjection H]

end TauCeti
