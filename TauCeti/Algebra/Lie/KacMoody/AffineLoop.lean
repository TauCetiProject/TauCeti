/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Algebra.Lie.KacMoody.Basic
public import TauCeti.Algebra.Lie.Loop.Extended
public import TauCeti.Algebra.Lie.Weights.IsSimple
public import TauCeti.Algebra.Lie.Weights.Sl2System
public import TauCeti.LinearAlgebra.Matrix.Cartan.Realization.Affine
public import TauCeti.LinearAlgebra.RootSystem.DualCoxeterNumber
-- Proof-only: triangular decomposition, ideal criterion, loop cohomology, and Serre relations.
import TauCeti.Algebra.Lie.KacMoody.Triangular
import TauCeti.Algebra.Lie.Killing.DualCoxeterNumber
import TauCeti.Algebra.Lie.Loop.Cocycle
import TauCeti.Algebra.Lie.Presentation.Serre.Killing
import TauCeti.Algebra.Lie.Weights.InvariantForm
import TauCeti.LinearAlgebra.RootSystem.HighestRoot.Basic

/-!
# Untwisted affine Kac–Moody algebras as extended loop algebras

Let `L` be a finite-dimensional simple Lie algebra over a field `K` of characteristic zero with a
splitting Cartan subalgebra `H`, let `b` be a base of the root system `rootSystem H` with highest
root `θ = b.highestRoot` and dual Coxeter number `h^∨ = b.dualCoxeterNumber`, and let
`x : Weight K H L → L` be a normalised family of root vectors (`TauCeti.IsSl2System x`).

This file proves **Kac's realization theorem for untwisted affine Kac–Moody algebras**
(`TauCeti.KacMoody.affineLoopEquiv`, Kac, Theorem 7.4): the Kac–Moody algebra
`PresentedLieAlgebra b.affineRealization` of the untwisted affine Cartan matrix
`b.affineCartanMatrixᵀ` is isomorphic as a Lie algebra to the extended affine loop algebra
`extendedResidueExtension (affineResidueForm b) ... = (K[t, t⁻¹] ⊗ L ⊕ K K) ⋊ K d`, where
`affineResidueForm b = -(2 h^∨)⁻¹ κ` is the negation of the normalized invariant form
`κ₀ = (2 h^∨)⁻¹ κ` (which satisfies `κ₀(θ^∨, θ^∨) = 2`).

Under `affineLoopEquiv b hx`:

* the Cartan element `(h, a, t)` goes to `1 ⊗ h + a K + t d`, so the canonical central element
  `c = ∑ₖ aₖ^∨ hₖ = (0, 1, 0)` goes to `K` and the scaling element `(0, 0, 1)` goes to `d`;
* the simple generators `eᵢ`, `fᵢ` go to the constant modes `1 ⊗ x(αᵢ)`, `1 ⊗ x(-αᵢ)`;
* the affine generators `e₀`, `f₀` go to `t ⊗ x(-θ)` and `t⁻¹ ⊗ x(θ)`.

The proof works over any field `K` of characteristic zero without assuming `K` is algebraically
closed:

1. **Existence (`affineLoopHom`)**: verifying the Chevalley and Serre relations in the extended
   loop algebra, using `κ₀(x(-θ), x(θ)) = 1` for `⁅e₀, f₀⁆ = K - θ^∨` and root-string truncation
   (`TauCeti.ad_pow_lie_eq_zero_of_rootSpace_sub_eq_bot`) for the Serre relations.
2. **Surjectivity (`affineLoopHom_surjective`)**: the constant modes generate `1 ⊗ L`, simplicity
   of `L` propagates each degree `n` from a single nonzero mode `tⁿ ⊗ v` to all of `tⁿ ⊗ L`, and
   `c` and `d` hit `K` and `d`.
3. **Injectivity (`affineLoopHom_injective`)**: the kernel `I` intersects the Cartan subalgebra
   trivially and is killed by `c`. Passing to the quotient of the derived subalgebra `𝔤'` by
   `⁅𝔤', I'⁆` produces a central extension of `loopAlgebra K ℤ L`; the classification of 2-cocycles
   on `loopAlgebra K ℤ L` (`TauCeti.LieAlgebra.LoopAlgebra.twoCocycle_eq_span_sup_range_d₁₂`)
   together with uniqueness of invariant forms on split simple Lie algebras
   (`TauCeti.LieAlgebra.IsKilling.exists_eq_smul_killingForm_of_isSimple`) forces `⁅𝔤', I'⁆ = I'`,
   whence `I = ⊥` by the ideal criterion
   `TauCeti.KacMoody.lieIdeal_eq_bot_of_disjoint_cartan_of_derived_eq_self`.

Pulling back `extendedBilinForm` along `affineLoopEquiv` yields the standard nondegenerate
symmetric invariant bilinear form `affineInvariantForm b hx` on
`PresentedLieAlgebra b.affineRealization`, and composing with `extendedLevelEquiv` identifies the
presented algebra with the extended loop algebra at any nonzero multiple of the normalized form
(`affineLoopEquivOfUnit`).

## Main definitions

* `TauCeti.KacMoody.normalizedKillingForm`: the normalized invariant form `κ₀ = (2 h^∨)⁻¹ κ` on `L`.
* `TauCeti.KacMoody.affineResidueForm`: `-κ₀`, the form used for Mathlib's residue cocycle.
* `TauCeti.KacMoody.affineLoopHom`: the Lie homomorphism from
  `PresentedLieAlgebra b.affineRealization` to the extended affine loop algebra.
* `TauCeti.KacMoody.affineLoopEquiv`: **Kac's isomorphism** between
  `PresentedLieAlgebra b.affineRealization` and the extended affine loop algebra.
* `TauCeti.KacMoody.affineInvariantForm`: the standard nondegenerate symmetric invariant bilinear
  form on `PresentedLieAlgebra b.affineRealization`.
* `TauCeti.KacMoody.affineLoopEquivOfUnit`: the isomorphism to the extended affine loop algebra
  for any nonzero scalar multiple `u • affineResidueForm b`.

## Main results

* `TauCeti.KacMoody.affineLoopHom_surjective` and `TauCeti.KacMoody.affineLoopHom_injective`:
  bijectivity of `affineLoopHom`.
* `TauCeti.KacMoody.cartanElement_affineRealization_injective`: the Cartan realization embeds
  injectively in the presented affine Kac–Moody algebra.
* `TauCeti.KacMoody.affineInvariantForm_isSymm`,
  `TauCeti.KacMoody.affineInvariantForm_lieInvariant`, and
  `TauCeti.KacMoody.affineInvariantForm_nondegenerate`: symmetry, invariance, and
  nondegeneracy of the standard affine invariant form, together with its explicit values on the
  Cartan, central, scaling, and Chevalley generators.

## References

* V. G. Kac, *Infinite-Dimensional Lie Algebras*, 3rd ed., §6.2 and §7.2–7.4 (especially Theorem
  7.4), for the realization of untwisted affine Kac–Moody algebras as extended loop algebras and
  their standard invariant bilinear form.
-/

public section

noncomputable section

open scoped Matrix TensorProduct
open LieAlgebra LieAlgebra.IsKilling LieAlgebra.LoopAlgebra LieModule
open _root_.LieModule.Cohomology
open _root_.LieAlgebra.ofTwoCocycle (centralElement centralElement_mem_center)
open TauCeti.LieAlgebra.LoopAlgebra

namespace TauCeti.KacMoody

section NormalizedForm

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsSimple K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base)

/-- **The normalized invariant bilinear form** `κ₀ = (2 h^∨)⁻¹ κ` on a split simple Lie algebra
`L`, normalized so that `κ₀(θ^∨, θ^∨) = 2` for the coroot of the highest root `θ`. -/
def normalizedKillingForm : LinearMap.BilinForm K L :=
  (2 * (b.dualCoxeterNumber : K))⁻¹ • killingForm K L

/-- `normalizedKillingForm b` is symmetric. -/
theorem normalizedKillingForm_isSymm : (normalizedKillingForm b).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ ?_
  have h := (LieModule.traceForm_isSymm K L L).eq x y
  simp only [RingHom.id_apply] at h
  simp only [normalizedKillingForm, LinearMap.smul_apply, smul_eq_mul, killingForm, h]

/-- `normalizedKillingForm b` is `L`-invariant. -/
theorem normalizedKillingForm_lieInvariant : (normalizedKillingForm b).lieInvariant L := by
  intro x y z
  simp only [normalizedKillingForm, LinearMap.smul_apply, smul_eq_mul]
  rw [LieModule.traceForm_lieInvariant K L L x y z, mul_neg]

/-- `normalizedKillingForm b` is nondegenerate. -/
theorem normalizedKillingForm_nondegenerate : (normalizedKillingForm b).Nondegenerate := by
  have hc : (2 * (b.dualCoxeterNumber : K))⁻¹ ≠ 0 :=
    inv_ne_zero (mul_ne_zero two_ne_zero (b.cast_dualCoxeterNumber_ne_zero (R := K)))
  refine ⟨fun x hx ↦ (killingForm_nondegenerate K L).1 x fun y ↦ ?_,
    fun y hy ↦ (killingForm_nondegenerate K L).2 y fun x ↦ ?_⟩
  · have h := hx y
    simp only [normalizedKillingForm, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  · have h := hy x
    simp only [normalizedKillingForm, LinearMap.smul_apply, smul_eq_mul] at h
    exact (mul_eq_zero.mp h).resolve_left hc

/-- The normalized form takes the value `2` on `(θ^∨, θ^∨)`. -/
theorem normalizedKillingForm_coroot_highestRoot :
    normalizedKillingForm b ((rootSystem H).coroot b.highestRoot : L)
      ((rootSystem H).coroot b.highestRoot : L) = 2 :=
  b.inv_smul_killingForm_coroot_highestRoot

/-- On `H`, pairing with `θ^∨` under `normalizedKillingForm b` evaluates the highest root `θ`. -/
theorem normalizedKillingForm_coroot_highestRoot_apply (h : H) :
    normalizedKillingForm b ((rootSystem H).coroot b.highestRoot : L) (h : L) =
      (rootSystem H).root b.highestRoot h := by
  have hh := b.cast_dualCoxeterNumber_ne_zero (R := K)
  rw [normalizedKillingForm, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    ← TauCeti.cartanEquivDual_apply_apply_eq_killingForm, rootSystem_coroot_apply,
    TauCeti.cartanEquivDual_coroot]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [← rootSystem_root_apply, b.invForm_root_highestRoot, inv_inv]
  field_simp

/-- On `H`, pairing with a simple coroot `αᵢ^∨` under `normalizedKillingForm b` evaluates
`(aᵢ / aᵢ^∨) * αᵢ`. -/
theorem normalizedKillingForm_coroot_simple_apply (i : b.support) (h : H) :
    normalizedKillingForm b ((rootSystem H).coroot i : L) (h : L) =
      ((b.affineMarks (some i) : K) / (b.affineComarks (some i) : K)) *
        (rootSystem H).root i h := by
  have hh := b.cast_dualCoxeterNumber_ne_zero (R := K)
  have hcom : (b.affineComarks (some i) : K) ≠ 0 := by
    exact_mod_cast (b.affineComarks_pos (some i)).ne'
  have hlen : (b.affineComarks (some i) : K) * (b.dualCoxeterNumber : K)⁻¹ =
      (b.affineMarks (some i) : K) *
        TauCeti.invForm ((rootSystem H).root i) ((rootSystem H).root i) := by
    have hmul := b.affineComarks_mul_form_highestRoot (TauCeti.rootInvariantForm (H := H)) i
    simpa only [TauCeti.rootInvariantForm_form, zsmul_eq_mul, b.invForm_root_highestRoot] using hmul
  have hinv_ne : TauCeti.invForm ((rootSystem H).root i) ((rootSystem H).root i) ≠ 0 := by
    simpa only [rootSystem_root_apply] using
      TauCeti.invForm_self_ne_zero (H.isNonZero_coe_root i.1)
  rw [normalizedKillingForm, LinearMap.smul_apply, LinearMap.smul_apply, smul_eq_mul,
    ← TauCeti.cartanEquivDual_apply_apply_eq_killingForm, rootSystem_coroot_apply,
    TauCeti.cartanEquivDual_coroot]
  simp only [LinearMap.smul_apply, smul_eq_mul]
  rw [← rootSystem_root_apply]
  have hlen' : (b.affineComarks (some i) : K) =
      (b.affineMarks (some i) : K) *
        TauCeti.invForm ((rootSystem H).root i) ((rootSystem H).root i) *
        (b.dualCoxeterNumber : K) := by
    field_simp at hlen
    linear_combination hlen
  have hratio : (2 * (b.dualCoxeterNumber : K))⁻¹ *
      (2 * (TauCeti.invForm ((rootSystem H).root i) ((rootSystem H).root i))⁻¹) =
      (b.affineMarks (some i) : K) / (b.affineComarks (some i) : K) := by
    field_simp
    rw [hlen']
    ring
  rw [← mul_assoc, hratio]

/-- For any invariant bilinear form `Φ` on `L` and any normalized root-vector family `x`,
`2 * Φ(x α, x (-α)) = Φ(α^∨, α^∨)`. -/
private theorem two_mul_apply_root_neg_eq_coroot {Φ : LinearMap.BilinForm K L}
    (hΦ : Φ.lieInvariant L) {x : Weight K H L → L} (hx : IsSl2System x)
    {α : Weight K H L} (hα : α.IsNonZero) :
    2 * Φ (x α) (x (-α)) = Φ (coroot α : L) (coroot α : L) := by
  have hinv := hΦ (x α) (coroot α : L) (x (-α))
  have hbra : ⁅x α, (coroot α : L)⁆ = -(2 : K) • x α := by
    rw [← lie_skew, hx.lie_coroot α α, root_apply_coroot hα, neg_smul]
  rw [hbra, hx.lie_neg α hα, map_smul, LinearMap.smul_apply, smul_eq_mul] at hinv
  linear_combination -hinv

/-- Pairing opposite root vectors of a normalized family under `normalizedKillingForm b`:
`κ₀(x α, x (-α)) = ½ κ₀(α^∨, α^∨)`. -/
theorem normalizedKillingForm_root_neg {x : Weight K H L → L} (hx : IsSl2System x)
    {α : Weight K H L} (hα : α.IsNonZero) :
    normalizedKillingForm b (x α) (x (-α)) =
      (2 : K)⁻¹ * normalizedKillingForm b (coroot α : L) (coroot α : L) := by
  have h := two_mul_apply_root_neg_eq_coroot (normalizedKillingForm_lieInvariant b) hx hα
  linear_combination h / 2

/-- For the highest root `θ`, `κ₀(x θ, x (-θ)) = 1`. -/
@[simp]
theorem normalizedKillingForm_highestRoot_neg {x : Weight K H L → L} (hx : IsSl2System x) :
    normalizedKillingForm b (x b.highestRoot.1) (x (-b.highestRoot.1)) = 1 := by
  rw [normalizedKillingForm_root_neg b hx (H.isNonZero_coe_root b.highestRoot),
    ← rootSystem_coroot_apply, normalizedKillingForm_coroot_highestRoot]
  norm_num

/-- For the highest root `θ`, `κ₀(x (-θ), x θ) = 1`. -/
@[simp]
theorem normalizedKillingForm_neg_highestRoot {x : Weight K H L → L} (hx : IsSl2System x) :
    normalizedKillingForm b (x (-b.highestRoot.1)) (x b.highestRoot.1) = 1 := by
  rw [(normalizedKillingForm_isSymm b).eq, normalizedKillingForm_highestRoot_neg b hx]

/-- For a simple root `αᵢ`, `κ₀(x αᵢ, x (-αᵢ)) = aᵢ / aᵢ^∨`. -/
theorem normalizedKillingForm_simple_neg {x : Weight K H L → L} (hx : IsSl2System x)
    (i : b.support) :
    normalizedKillingForm b (x i.1.1) (x (-i.1.1)) =
      (b.affineMarks (some i) : K) / (b.affineComarks (some i) : K) := by
  rw [normalizedKillingForm_root_neg b hx (H.isNonZero_coe_root i.1),
    ← rootSystem_coroot_apply, normalizedKillingForm_coroot_simple_apply b i]
  have h2 : (rootSystem H).root i ((rootSystem H).coroot i) = 2 := by
    rw [rootSystem_root_apply, rootSystem_coroot_apply, Weight.toLinear_apply,
      root_apply_coroot (H.isNonZero_coe_root i.1)]
  rw [h2]
  ring

/-- **The affine residue form** `-κ₀` on `L`. With Mathlib's residue cocycle convention
`c(x_m, y_n) = n Φ(x, y) δ_{m+n,0}`, choosing `Φ = -κ₀` makes `⁅t ⊗ x(-θ), t⁻¹ ⊗ x(θ)⁆ = K - θ^∨`
and makes `extendedBilinForm Φ` restrict to `+κ₀` on constant loops. -/
def affineResidueForm : LinearMap.BilinForm K L :=
  -normalizedKillingForm b

/-- `affineResidueForm b` is symmetric. -/
theorem affineResidueForm_isSymm : (affineResidueForm b).IsSymm := by
  refine LinearMap.BilinForm.isSymm_def.mpr fun x y ↦ ?_
  simp only [affineResidueForm, LinearMap.neg_apply, (normalizedKillingForm_isSymm b).eq x y]

/-- `affineResidueForm b` is `L`-invariant. -/
theorem affineResidueForm_lieInvariant : (affineResidueForm b).lieInvariant L := by
  intro x y z
  simp only [affineResidueForm, LinearMap.neg_apply]
  linear_combination -normalizedKillingForm_lieInvariant b x y z

/-- `affineResidueForm b` is nondegenerate. -/
theorem affineResidueForm_nondegenerate : (affineResidueForm b).Nondegenerate := by
  refine ⟨fun x hx ↦ (normalizedKillingForm_nondegenerate b).1 x fun y ↦ ?_,
    fun y hy ↦ (normalizedKillingForm_nondegenerate b).2 y fun x ↦ ?_⟩
  · simpa [affineResidueForm] using hx y
  · simpa [affineResidueForm] using hy x

end NormalizedForm

/-! ### The untwisted affine loop homomorphism and Kac's Theorem 7.4 -/

section AffineLoop

variable {K L : Type*} [Field K] [CharZero K] [LieRing L] [LieAlgebra K L]
  [FiniteDimensional K L] [IsSimple K L] {H : LieSubalgebra K L}
  [H.IsCartanSubalgebra] [IsTriangularizable K H L]
  (b : (rootSystem H).Base)

local notation "Φ" => affineResidueForm b
local notation "hΦ" => affineResidueForm_lieInvariant b
local notation "hΦs" => affineResidueForm_isSymm b
local notation "c₀" => twoCocycleOfBilinear K ℤ L Φ hΦ hΦs
local notation "E'" => extendedResidueExtension Φ hΦ hΦs

/-- The Cartan map `H × K × K → E'` sending `(h, a, t)` to `1 ⊗ h + a K + t d`. -/
private def affineLoopCartan : H × K × K →ₗ[K] E' where
  toFun v :=
    mode Φ hΦ hΦs 0 (v.1 : L) +
      v.2.1 • toExtendedResidueExtension Φ hΦ hΦs (centralElement c₀) +
      v.2.2 • degreeElement Φ hΦ hΦs
  map_add' u v := by
    simp only [Prod.fst_add, Prod.snd_add, AddMemClass.coe_add, map_add, add_smul]
    abel
  map_smul' r v := by
    simp only [Prod.smul_fst, Prod.smul_snd, SetLike.val_smul, map_smul, smul_add, smul_eq_mul,
      smul_smul, RingHom.id_apply]

/-- The raising generators in the extended affine loop algebra: `e₀ = t ⊗ x(-θ)` and
`eᵢ = 1 ⊗ x(αᵢ)`. -/
private def affineLoopE (x : Weight K H L → L) : Option b.support → E'
  | none => mode Φ hΦ hΦs 1 (x (-b.highestRoot.1))
  | some i => mode Φ hΦ hΦs 0 (x i.1.1)

/-- The lowering generators in the extended affine loop algebra: `f₀ = t⁻¹ ⊗ x(θ)` and
`fᵢ = 1 ⊗ x(-αᵢ)`. -/
private def affineLoopF (x : Weight K H L → L) : Option b.support → E'
  | none => mode Φ hΦ hΦs (-1) (x b.highestRoot.1)
  | some i => mode Φ hΦ hΦs 0 (x (-i.1.1))

/-- The sum of the highest root and a simple root is not a root, so its root space is `⊥`. -/
private theorem rootSpace_highestRoot_add_simple_eq_bot (j : b.support) :
    rootSpace H (⇑b.highestRoot.1 + ⇑j.1.1) = ⊥ := by
  by_contra hbot
  have hne : ⇑b.highestRoot.1 + ⇑j.1.1 ≠ 0 := by
    intro h0
    have hneg : (rootSystem H).root b.highestRoot =
        (rootSystem H).root ((rootSystem H).reflectionPerm j.1 j.1) := by
      rw [RootPairing.root_reflectionPerm, RootPairing.reflection_apply_self]
      ext h
      have hh := congrFun h0 h
      simp only [Pi.add_apply, Pi.zero_apply] at hh
      simp only [rootSystem_root_apply, Weight.toLinear_apply, LinearMap.neg_apply]
      linear_combination hh
    have heq := (rootSystem H).root.injective hneg
    have hpos : b.highestRoot ∈ TauCeti.posRoots (rootSystem H) b :=
      (TauCeti.mem_posRoots (rootSystem H) b _).mpr b.isPos_highestRoot
    have hjpos : j.1 ∈ TauCeti.posRoots (rootSystem H) b :=
      (TauCeti.mem_posRoots (rootSystem H) b _).mpr (b.isPos_of_mem_support j.2)
    rw [heq] at hpos
    exact TauCeti.reflectionPerm_self_notMem_posRoots (rootSystem H) b hjpos hpos
  let χ : Weight K H L := ⟨⇑b.highestRoot.1 + ⇑j.1.1, hbot⟩
  have hχ : χ.IsNonZero := hne
  have hmem : (rootSystem H).root b.highestRoot + (rootSystem H).root j.1 ∈
      Set.range (rootSystem H).root :=
    ⟨⟨χ, by simpa [LieSubalgebra.root] using hχ⟩, LinearMap.ext fun h ↦ rfl⟩
  exact b.root_highestRoot_add_root_notMem j.2 hmem

/-- The root space of `-θ - αⱼ` is `⊥`. -/
private theorem rootSpace_neg_highestRoot_sub_simple_eq_bot (j : b.support) :
    rootSpace H (-⇑b.highestRoot.1 - ⇑j.1.1) = ⊥ := by
  by_contra hbot
  let ψ : Weight K H L := ⟨-⇑b.highestRoot.1 - ⇑j.1.1, hbot⟩
  have hneg_ne : rootSpace H (⇑(-ψ)) ≠ ⊥ := (-ψ).genWeightSpace_ne_bot
  have hfun : (⇑(-ψ) : H → K) = ⇑b.highestRoot.1 + ⇑j.1.1 := by
    funext h
    change -((-⇑b.highestRoot.1 - ⇑j.1.1) h) = ⇑b.highestRoot.1 h + ⇑j.1.1 h
    simp only [Pi.sub_apply, Pi.neg_apply]
    ring
  rw [hfun] at hneg_ne
  exact hneg_ne (rootSpace_highestRoot_add_simple_eq_bot b j)

/-- Two modes of nonnegative degree bracket with no central term. -/
private theorem lie_mode_mode_of_nonneg {d m : ℤ} (hd : 0 ≤ d) (hm : 0 ≤ m) (u v : L) :
    ⁅mode Φ hΦ hΦs d u, mode Φ hΦ hΦs m v⁆ = mode Φ hΦ hΦs (d + m) ⁅u, v⁆ := by
  rw [lie_mode_mode]
  split_ifs with h
  · have hm0 : m = 0 := by omega
    simp [hm0]
  · simp

/-- Two modes of nonpositive degree bracket with no central term. -/
private theorem lie_mode_mode_of_nonpos {d m : ℤ} (hd : d ≤ 0) (hm : m ≤ 0) (u v : L) :
    ⁅mode Φ hΦ hΦs d u, mode Φ hΦ hΦs m v⁆ = mode Φ hΦ hΦs (d + m) ⁅u, v⁆ := by
  rw [lie_mode_mode]
  split_ifs with h
  · have hm0 : m = 0 := by omega
    simp [hm0]
  · simp

/-- Iterated `ad` of a nonnegative-degree mode on a nonnegative-degree mode stays a pure mode. -/
private theorem ad_mode_pow_of_nonneg {d m : ℤ} (hd : 0 ≤ d) (hm : 0 ≤ m) (u v : L) (n : ℕ) :
    (ad K E' (mode Φ hΦ hΦs d u) ^ n) (mode Φ hΦ hΦs m v) =
      mode Φ hΦ hΦs (n • d + m) ((ad K L u ^ n) v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnm : (0 : ℤ) ≤ n • d + m := by
      rw [nsmul_eq_mul]
      exact add_nonneg (mul_nonneg (Int.natCast_nonneg n) hd) hm
    rw [pow_succ', _root_.mul_apply_eq_comp, ih, pow_succ', _root_.mul_apply_eq_comp,
      ad_apply, ad_apply, lie_mode_mode_of_nonneg b hd hnm,
      show d + (n • d + m) = (n + 1) • d + m by simp only [nsmul_eq_mul]; push_cast; ring]

/-- Iterated `ad` of a nonpositive-degree mode on a nonpositive-degree mode stays a pure mode. -/
private theorem ad_mode_pow_of_nonpos {d m : ℤ} (hd : d ≤ 0) (hm : m ≤ 0) (u v : L) (n : ℕ) :
    (ad K E' (mode Φ hΦ hΦs d u) ^ n) (mode Φ hΦ hΦs m v) =
      mode Φ hΦ hΦs (n • d + m) ((ad K L u ^ n) v) := by
  induction n with
  | zero => simp
  | succ n ih =>
    have hnm : (n • d + m : ℤ) ≤ 0 := by
      have : (n • d : ℤ) ≤ 0 := by
        rw [nsmul_eq_mul]
        exact mul_nonpos_of_nonneg_of_nonpos (Int.natCast_nonneg n) hd
      omega
    rw [pow_succ', _root_.mul_apply_eq_comp, ih, pow_succ', _root_.mul_apply_eq_comp,
      ad_apply, ad_apply, lie_mode_mode_of_nonpos b hd hnm,
      show d + (n • d + m) = (n + 1) • d + m by simp only [nsmul_eq_mul]; push_cast; ring]

/-- The generators `affineLoopCartan`, `affineLoopE`, `affineLoopF` satisfy all defining relations
of the Kac–Moody algebra `PresentedLieAlgebra b.affineRealization`. -/
private theorem satisfiesRelations_affineLoop {x : Weight K H L → L} (hx : IsSl2System x) :
    SatisfiesRelations b.affineRealization (affineLoopCartan b) (affineLoopE b x)
      (affineLoopF b x) where
  lie_cartan_cartan u v := by
    rcases u with ⟨h₁, a₁, t₁⟩
    rcases v with ⟨h₂, a₂, t₂⟩
    have hK := (LieModule.mem_maxTrivSubmodule K E' E' _).1
      (toExtendedResidueExtension_centralElement_mem_center Φ hΦ hΦs)
    have hK_left (w : E') : ⁅toExtendedResidueExtension Φ hΦ hΦs (centralElement c₀), w⁆ = 0 := by
      rw [← lie_skew, hK w, neg_zero]
    have hH : ⁅(h₁ : L), (h₂ : L)⁆ = 0 := LieSubalgebra.lie_eq_zero_of_mem h₁.2 h₂.2
    simp only [affineLoopCartan, LinearMap.coe_mk, AddHom.coe_mk, add_lie, lie_add, smul_lie,
      lie_smul, hK, hK_left, lie_degreeElement_mode, lie_self, smul_zero, zero_zsmul, add_zero]
    have hd0 : ⁅mode Φ hΦ hΦs 0 (h₁ : L), degreeElement Φ hΦ hΦs⁆ = 0 := by
      rw [← lie_skew, lie_degreeElement_mode, zero_zsmul, neg_zero]
    rw [hd0, smul_zero, add_zero, lie_mode_mode_of_nonneg b le_rfl le_rfl, hH, map_zero]
  lie_cartan_positive u k := by
    rcases u with ⟨h, a, t⟩
    have hK := (LieModule.mem_maxTrivSubmodule K E' E' _).1
      (toExtendedResidueExtension_centralElement_mem_center Φ hΦ hΦs)
    have hK_left (w : E') : ⁅toExtendedResidueExtension Φ hΦ hΦs (centralElement c₀), w⁆ = 0 := by
      rw [← lie_skew, hK w, neg_zero]
    rcases k with _ | i
    · simp only [affineLoopCartan, affineLoopE, LinearMap.coe_mk, AddHom.coe_mk, add_lie, smul_lie,
        hK_left, smul_zero, add_zero, lie_degreeElement_mode, one_zsmul,
        lie_mode_mode_of_nonneg b le_rfl zero_le_one, zero_add]
      have hbra : ⁅(h : L), x (-b.highestRoot.1)⁆ =
          (-(rootSystem H).root b.highestRoot h) • x (-b.highestRoot.1) := by
        rw [← LieSubalgebra.coe_bracket_of_module,
          lie_eq_smul_of_mem_rootSpace (hx.mem_rootSpace (-b.highestRoot.1)) h]
        simp [rootSystem_root_apply, Weight.toLinear_apply]
      rw [hbra, map_smul, b.affineRealization_root_none, rootSystem_toLinearMap_apply,
        neg_smul, sub_smul]
      abel
    · simp only [affineLoopCartan, affineLoopE, LinearMap.coe_mk, AddHom.coe_mk, add_lie, smul_lie,
        hK_left, smul_zero, add_zero, lie_degreeElement_mode, zero_zsmul,
        lie_mode_mode_of_nonneg b le_rfl le_rfl]
      have hbra : ⁅(h : L), x i.1.1⁆ = (rootSystem H).root i.1 h • x i.1.1 := by
        rw [← LieSubalgebra.coe_bracket_of_module,
          lie_eq_smul_of_mem_rootSpace (hx.mem_rootSpace i.1.1) h]
        simp [rootSystem_root_apply, Weight.toLinear_apply]
      rw [hbra, map_smul, b.affineRealization_root_some, rootSystem_toLinearMap_apply]
  lie_cartan_negative u k := by
    rcases u with ⟨h, a, t⟩
    have hK := (LieModule.mem_maxTrivSubmodule K E' E' _).1
      (toExtendedResidueExtension_centralElement_mem_center Φ hΦ hΦs)
    have hK_left (w : E') : ⁅toExtendedResidueExtension Φ hΦ hΦs (centralElement c₀), w⁆ = 0 := by
      rw [← lie_skew, hK w, neg_zero]
    rcases k with _ | i
    · simp only [affineLoopCartan, affineLoopF, LinearMap.coe_mk, AddHom.coe_mk, add_lie, smul_lie,
        hK_left, smul_zero, add_zero, lie_degreeElement_mode, neg_smul, one_zsmul, smul_neg,
        lie_mode_mode_of_nonpos b le_rfl (by norm_num : (-1 : ℤ) ≤ 0), zero_add]
      have hbra : ⁅(h : L), x b.highestRoot.1⁆ =
          (rootSystem H).root b.highestRoot h • x b.highestRoot.1 := by
        rw [← LieSubalgebra.coe_bracket_of_module,
          lie_eq_smul_of_mem_rootSpace (hx.mem_rootSpace b.highestRoot.1) h]
        simp [rootSystem_root_apply, Weight.toLinear_apply]
      rw [hbra, map_smul, b.affineRealization_root_none, rootSystem_toLinearMap_apply, sub_smul]
      abel
    · simp only [affineLoopCartan, affineLoopF, LinearMap.coe_mk, AddHom.coe_mk, add_lie, smul_lie,
        hK_left, smul_zero, add_zero, lie_degreeElement_mode, zero_zsmul,
        lie_mode_mode_of_nonpos b le_rfl le_rfl]
      have hbra : ⁅(h : L), x (-i.1.1)⁆ = -((rootSystem H).root i.1 h • x (-i.1.1)) := by
        rw [← LieSubalgebra.coe_bracket_of_module,
          lie_eq_smul_of_mem_rootSpace (hx.mem_rootSpace (-i.1.1)) h]
        simp [rootSystem_root_apply, Weight.toLinear_apply]
      rw [hbra, map_neg, map_smul, b.affineRealization_root_some, rootSystem_toLinearMap_apply]
  lie_positive_negative_self k := by
    rcases k with _ | i
    · have hΦ1 : Φ (x (-b.highestRoot.1)) (x b.highestRoot.1) = -1 := by
        simp [affineResidueForm, normalizedKillingForm_neg_highestRoot b hx]
      have hbra : ⁅x (-b.highestRoot.1), x b.highestRoot.1⁆ =
          ((-(rootSystem H).coroot b.highestRoot : H) : L) := by
        rw [← lie_skew, hx.lie_neg b.highestRoot.1 (H.isNonZero_coe_root b.highestRoot),
          rootSystem_coroot_apply, NegMemClass.coe_neg]
      simp only [affineLoopE, affineLoopF, affineLoopCartan, LinearMap.coe_mk, AddHom.coe_mk,
        b.affineRealization_coroot_none, lie_mode_mode, add_neg_cancel, ↓reduceIte,
        Int.cast_neg, Int.cast_one, hΦ1, mul_neg, mul_one, neg_neg, one_smul, zero_smul, add_zero,
        hbra]
    · simp only [affineLoopE, affineLoopF, affineLoopCartan, LinearMap.coe_mk, AddHom.coe_mk,
        b.affineRealization_coroot_some, lie_mode_mode_of_nonneg b le_rfl le_rfl, add_zero,
        zero_smul]
      rw [hx.lie_neg i.1.1 (H.isNonZero_coe_root i.1), rootSystem_coroot_apply]
  lie_positive_negative_of_ne k l hkl := by
    rcases k with _ | i <;> rcases l with _ | j
    · exact absurd rfl hkl
    · simp only [affineLoopE, affineLoopF, lie_mode_mode_of_nonneg b zero_le_one le_rfl, add_zero]
      have h0 : ⁅x (-b.highestRoot.1), x (-j.1.1)⁆ = 0 := by
        refine hx.lie_eq_zero_of_rootSpace_add_eq_bot (-b.highestRoot.1) (-j.1.1) ?_
        simpa only [Weight.coe_neg, ← sub_eq_add_neg] using
          rootSpace_neg_highestRoot_sub_simple_eq_bot b j
      rw [h0, map_zero]
    · simp only [affineLoopE, affineLoopF,
        lie_mode_mode_of_nonpos b le_rfl (by norm_num : (-1 : ℤ) ≤ 0), zero_add]
      have h0 : ⁅x i.1.1, x b.highestRoot.1⁆ = 0 := by
        refine hx.lie_eq_zero_of_rootSpace_add_eq_bot i.1.1 b.highestRoot.1 ?_
        rw [add_comm]
        exact rootSpace_highestRoot_add_simple_eq_bot b i
      rw [h0, map_zero]
    · have hij : i ≠ j := fun h ↦ hkl (congrArg some h)
      simp only [affineLoopE, affineLoopF, lie_mode_mode_of_nonneg b le_rfl le_rfl, add_zero]
      have h0 : ⁅x i.1.1, x (-j.1.1)⁆ = 0 := by
        refine hx.lie_eq_zero_of_rootSpace_add_eq_bot i.1.1 (-j.1.1) ?_
        simpa only [Weight.coe_neg, ← sub_eq_add_neg] using
          TauCeti.rootSpace_sub_eq_bot_of_base b hij
      rw [h0, map_zero]
  serre_positive k l := by
    rcases k with _ | i <;> rcases l with _ | j
    · simp
    · simp only [affineLoopE, lie_mode_mode_of_nonneg b zero_le_one le_rfl, add_zero,
        ad_mode_pow_of_nonneg b zero_le_one zero_le_one]
      have hn : ((b.affineCartanMatrixᵀ none (some j) : ℤ) : K) =
          j.1.1 (coroot (-b.highestRoot.1)) := by
        have hp := (rootSystem H).algebraMap_pairingIn ℤ j.1 b.highestRoot
        rw [rootSystem_pairing_apply, algebraMap_int_eq, Int.coe_castRingHom] at hp
        dsimp only at hp
        rw [Matrix.transpose_apply, b.affineCartanMatrix_some_none, Int.cast_neg, coroot_neg,
          map_neg, hp]
      have hsub : rootSpace H (⇑j.1.1 - ⇑(-b.highestRoot.1)) = ⊥ := by
        rw [Weight.coe_neg, sub_neg_eq_add, add_comm]
        exact rootSpace_highestRoot_add_simple_eq_bot b j
      rw [TauCeti.ad_pow_lie_eq_zero_of_rootSpace_sub_eq_bot
        (Weight.isNonZero_neg.2 (H.isNonZero_coe_root b.highestRoot)) hsub hn
        (hx.mem_rootSpace (-b.highestRoot.1)) (hx.mem_rootSpace j.1.1), map_zero]
    · simp only [affineLoopE, lie_mode_mode_of_nonneg b le_rfl zero_le_one, zero_add,
        ad_mode_pow_of_nonneg b le_rfl zero_le_one]
      have hn : ((b.affineCartanMatrixᵀ (some i) none : ℤ) : K) =
          (-b.highestRoot.1) (coroot i.1.1) := by
        have hp := (rootSystem H).algebraMap_pairingIn ℤ b.highestRoot i.1
        rw [rootSystem_pairing_apply, algebraMap_int_eq, Int.coe_castRingHom] at hp
        dsimp only at hp
        rw [Matrix.transpose_apply, b.affineCartanMatrix_none_some, Int.cast_neg, Weight.coe_neg,
          Pi.neg_apply, hp]
      have hsub : rootSpace H (⇑(-b.highestRoot.1) - ⇑i.1.1) = ⊥ := by
        rw [Weight.coe_neg]
        exact rootSpace_neg_highestRoot_sub_simple_eq_bot b i
      rw [TauCeti.ad_pow_lie_eq_zero_of_rootSpace_sub_eq_bot
        (H.isNonZero_coe_root i.1) hsub hn (hx.mem_rootSpace i.1.1)
        (hx.mem_rootSpace (-b.highestRoot.1)), map_zero]
    · rcases eq_or_ne i j with rfl | hij
      · simp
      · simp only [affineLoopE, lie_mode_mode_of_nonneg b le_rfl le_rfl, add_zero,
          ad_mode_pow_of_nonneg b le_rfl le_rfl]
        have hn : ((b.affineCartanMatrixᵀ (some i) (some j) : ℤ) : K) = j.1.1 (coroot i.1.1) := by
          rw [Matrix.transpose_apply, b.affineCartanMatrix_some_some]
          exact TauCeti.cartanMatrix_eq_apply_coroot b i j
        rw [TauCeti.ad_pow_lie_eq_zero_of_rootSpace_sub_eq_bot (H.isNonZero_coe_root i.1)
          (TauCeti.rootSpace_sub_eq_bot_of_base b hij.symm) hn
          (hx.mem_rootSpace i.1.1) (hx.mem_rootSpace j.1.1), map_zero]
  serre_negative k l := by
    rcases k with _ | i <;> rcases l with _ | j
    · simp
    · simp only [affineLoopF,
        lie_mode_mode_of_nonpos b (by norm_num : (-1 : ℤ) ≤ 0) le_rfl, add_zero,
        ad_mode_pow_of_nonpos b (by norm_num : (-1 : ℤ) ≤ 0) (by norm_num : (-1 : ℤ) ≤ 0)]
      have hn : ((b.affineCartanMatrixᵀ none (some j) : ℤ) : K) =
          (-j.1.1) (coroot b.highestRoot.1) := by
        have hp := (rootSystem H).algebraMap_pairingIn ℤ j.1 b.highestRoot
        rw [rootSystem_pairing_apply, algebraMap_int_eq, Int.coe_castRingHom] at hp
        dsimp only at hp
        rw [Matrix.transpose_apply, b.affineCartanMatrix_some_none, Int.cast_neg, Weight.coe_neg,
          Pi.neg_apply, hp]
      have hsub : rootSpace H (⇑(-j.1.1) - ⇑b.highestRoot.1) = ⊥ := by
        rw [Weight.coe_neg, sub_eq_add_neg, add_comm, ← sub_eq_add_neg]
        exact rootSpace_neg_highestRoot_sub_simple_eq_bot b j
      rw [TauCeti.ad_pow_lie_eq_zero_of_rootSpace_sub_eq_bot
        (H.isNonZero_coe_root b.highestRoot) hsub hn
        (hx.mem_rootSpace b.highestRoot.1) (hx.mem_rootSpace (-j.1.1)), map_zero]
    · simp only [affineLoopF,
        lie_mode_mode_of_nonpos b le_rfl (by norm_num : (-1 : ℤ) ≤ 0), zero_add,
        ad_mode_pow_of_nonpos b le_rfl (by norm_num : (-1 : ℤ) ≤ 0)]
      have hn : ((b.affineCartanMatrixᵀ (some i) none : ℤ) : K) =
          b.highestRoot.1 (coroot (-i.1.1)) := by
        have hp := (rootSystem H).algebraMap_pairingIn ℤ b.highestRoot i.1
        rw [rootSystem_pairing_apply, algebraMap_int_eq, Int.coe_castRingHom] at hp
        dsimp only at hp
        rw [Matrix.transpose_apply, b.affineCartanMatrix_none_some, Int.cast_neg, coroot_neg,
          map_neg, hp]
      have hsub : rootSpace H (⇑b.highestRoot.1 - ⇑(-i.1.1)) = ⊥ := by
        rw [Weight.coe_neg, sub_neg_eq_add]
        exact rootSpace_highestRoot_add_simple_eq_bot b i
      rw [TauCeti.ad_pow_lie_eq_zero_of_rootSpace_sub_eq_bot
        (Weight.isNonZero_neg.2 (H.isNonZero_coe_root i.1)) hsub hn
        (hx.mem_rootSpace (-i.1.1)) (hx.mem_rootSpace b.highestRoot.1), map_zero]
    · rcases eq_or_ne i j with rfl | hij
      · simp
      · simp only [affineLoopF, lie_mode_mode_of_nonpos b le_rfl le_rfl, add_zero,
          ad_mode_pow_of_nonpos b le_rfl le_rfl]
        have hn : ((b.affineCartanMatrixᵀ (some i) (some j) : ℤ) : K) =
            (-j.1.1) (coroot (-i.1.1)) := by
          rw [Matrix.transpose_apply, b.affineCartanMatrix_some_some, coroot_neg, Weight.coe_neg,
            Pi.neg_apply, map_neg, neg_neg]
          exact TauCeti.cartanMatrix_eq_apply_coroot b i j
        have hsub : rootSpace H (⇑(-j.1.1) - ⇑(-i.1.1)) = ⊥ := by
          rw [Weight.coe_neg, Weight.coe_neg, neg_sub_neg]
          exact TauCeti.rootSpace_sub_eq_bot_of_base b hij
        rw [TauCeti.ad_pow_lie_eq_zero_of_rootSpace_sub_eq_bot
          (Weight.isNonZero_neg.2 (H.isNonZero_coe_root i.1)) hsub hn
          (hx.mem_rootSpace (-i.1.1)) (hx.mem_rootSpace (-j.1.1)), map_zero]

/-- **The untwisted affine loop homomorphism** from `PresentedLieAlgebra b.affineRealization` to
the extended affine loop algebra `extendedResidueExtension (affineResidueForm b) ...`. -/
def affineLoopHom {x : Weight K H L → L} (hx : IsSl2System x) :
    PresentedLieAlgebra b.affineRealization →ₗ⁅K⁆ E' :=
  KacMoody.lift (satisfiesRelations_affineLoop b hx)

@[simp]
theorem affineLoopHom_cartanElement {x : Weight K H L → L} (hx : IsSl2System x)
    (h : H) (a t : K) :
    affineLoopHom b hx (cartanElement b.affineRealization (h, a, t)) =
      mode Φ hΦ hΦs 0 (h : L) +
        a • toExtendedResidueExtension Φ hΦ hΦs (centralElement c₀) +
        t • degreeElement Φ hΦ hΦs :=
  lift_cartanElement _ (h, a, t)

/-- `affineLoopHom` sends the canonical central element `c` to the central element of the
extended loop algebra. -/
theorem affineLoopHom_centralElement {x : Weight K H L → L} (hx : IsSl2System x) :
    affineLoopHom b hx (cartanElement b.affineRealization b.affineCentralElement) =
      toExtendedResidueExtension Φ hΦ hΦs (centralElement c₀) := by
  rw [b.affineCentralElement_eq, affineLoopHom_cartanElement]
  simp

/-- `affineLoopHom` sends the scaling element `d = (0, 0, 1)` to `degreeElement`. -/
theorem affineLoopHom_degreeElement {x : Weight K H L → L} (hx : IsSl2System x) :
    affineLoopHom b hx (cartanElement b.affineRealization (0, 0, 1)) =
      degreeElement Φ hΦ hΦs := by
  rw [affineLoopHom_cartanElement]
  simp

@[simp]
theorem affineLoopHom_positiveGenerator_none {x : Weight K H L → L} (hx : IsSl2System x) :
    affineLoopHom b hx (positiveGenerator b.affineRealization none) =
      mode Φ hΦ hΦs 1 (x (-b.highestRoot.1)) :=
  lift_positiveGenerator _ none

@[simp]
theorem affineLoopHom_positiveGenerator_some {x : Weight K H L → L} (hx : IsSl2System x)
    (i : b.support) :
    affineLoopHom b hx (positiveGenerator b.affineRealization (some i)) =
      mode Φ hΦ hΦs 0 (x i.1.1) :=
  lift_positiveGenerator _ (some i)

@[simp]
theorem affineLoopHom_negativeGenerator_none {x : Weight K H L → L} (hx : IsSl2System x) :
    affineLoopHom b hx (negativeGenerator b.affineRealization none) =
      mode Φ hΦ hΦs (-1) (x b.highestRoot.1) :=
  lift_negativeGenerator _ none

@[simp]
theorem affineLoopHom_negativeGenerator_some {x : Weight K H L → L} (hx : IsSl2System x)
    (i : b.support) :
    affineLoopHom b hx (negativeGenerator b.affineRealization (some i)) =
      mode Φ hΦ hΦs 0 (x (-i.1.1)) :=
  lift_negativeGenerator _ (some i)

/-- The canonical central element `c = ∑ aₖ^∨ hₖ` lies in the derived subalgebra `𝔤'`. -/
private theorem affineCentralElement_mem_range_serreHom [DecidableEq (Option b.support)] :
    cartanElement b.affineRealization b.affineCentralElement ∈
      (serreHom b.affineRealization).range := by
  refine ⟨∑ k : Option b.support, (b.affineComarks k : K) • serreH K b.affineCartanMatrixᵀ k, ?_⟩
  rw [b.affineCentralElement_def, map_sum, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, map_smul]
  exact congrArg _ (serreHom_serreH b.affineRealization k)

/-- The canonical central element `c` commutes with every element of
`PresentedLieAlgebra b.affineRealization`. -/
private theorem lie_affineCentralElement (u : PresentedLieAlgebra b.affineRealization) :
    ⁅cartanElement b.affineRealization b.affineCentralElement, u⁆ = 0 := by
  have hu : u ∈ LieSubalgebra.lieSpan K (PresentedLieAlgebra b.affineRealization)
      (Set.range (cartanElement b.affineRealization) ∪
        Set.range (positiveGenerator b.affineRealization) ∪
        Set.range (negativeGenerator b.affineRealization)) := by
    rw [lieSpan_generators_eq_top]
    trivial
  induction hu using LieSubalgebra.lieSpan_induction with
  | mem y hy =>
    rcases hy with (⟨h, rfl⟩ | ⟨k, rfl⟩) | ⟨k, rfl⟩
    · exact lie_cartanElement_cartanElement _ _ _
    · rw [lie_cartanElement_positiveGenerator, b.affineCentralElement_eq]
      rcases k with _ | i <;> simp
    · rw [lie_cartanElement_negativeGenerator, b.affineCentralElement_eq]
      rcases k with _ | i <;> simp
  | zero => simp
  | add _ _ _ _ h₁ h₂ => rw [lie_add, h₁, h₂, add_zero]
  | smul c _ _ h => rw [lie_smul, h, smul_zero]
  | lie _ _ _ _ h₁ h₂ => rw [leibniz_lie, h₁, h₂, zero_lie, lie_zero, add_zero]

/-- The derived subalgebra `𝔤' = (serreHom _).range` maps onto the residue central extension
`ĝ = toExtendedResidueExtension.range` under `affineLoopHom`. -/
private theorem range_affineLoopHom_comp_serreHom [DecidableEq (Option b.support)]
    {x : Weight K H L → L} (hx : IsSl2System x) :
    ((affineLoopHom b hx).comp (serreHom b.affineRealization)).range =
      (toExtendedResidueExtension Φ hΦ hΦs).range := by
  set R' := ((affineLoopHom b hx).comp (serreHom b.affineRealization)).range
  refine le_antisymm ?_ ?_
  · -- Every generator `eₖ`, `fₖ` maps into `toExtendedResidueExtension.range`.
    have hle : (serreHom b.affineRealization).range ≤
        (toExtendedResidueExtension Φ hΦ hΦs).range.comap (affineLoopHom b hx) := by
      rw [range_serreHom, LieSubalgebra.lieSpan_le]
      rintro _ (⟨k, rfl⟩ | ⟨k, rfl⟩)
      · rcases k with _ | i
        · exact ⟨_, (mode_apply Φ hΦ hΦs 1 (x (-b.highestRoot.1))).symm.trans
            (affineLoopHom_positiveGenerator_none b hx).symm⟩
        · exact ⟨_, (mode_apply Φ hΦ hΦs 0 (x i.1.1)).symm.trans
            (affineLoopHom_positiveGenerator_some b hx i).symm⟩
      · rcases k with _ | i
        · exact ⟨_, (mode_apply Φ hΦ hΦs (-1) (x b.highestRoot.1)).symm.trans
            (affineLoopHom_negativeGenerator_none b hx).symm⟩
        · exact ⟨_, (mode_apply Φ hΦ hΦs 0 (x (-i.1.1))).symm.trans
            (affineLoopHom_negativeGenerator_some b hx i).symm⟩
    rintro _ ⟨s, rfl⟩
    exact hle ⟨s, rfl⟩
  · -- First show every constant mode `mode 0 y` lies in `R'`.
    have hconst : ∀ y : L, mode Φ hΦ hΦs 0 y ∈ R' := by
      have hgen : LieSubalgebra.lieSpan K L
          (Set.range (fun i : b.support ↦ x i.1.1) ∪
            Set.range (fun i : b.support ↦ x (-i.1.1))) = ⊤ :=
        lieSpan_range_union_eq_top_of_mem_rootSpace b
          (fun i ↦ x i.1.1) (fun i ↦ x (-i.1.1))
          (fun i ↦ by
            simpa only [rootSystem_coroot_apply] using
              hx.isSl2Triple i.1.1 (H.isNonZero_coe_root i.1))
          (fun i ↦ hx.mem_rootSpace i.1.1)
          (fun i ↦ by simpa [Weight.coe_neg] using hx.mem_rootSpace (-i.1.1))
      have hle : (⊤ : LieSubalgebra K L) ≤ R'.comap (constHom Φ hΦ hΦs) := by
        rw [← hgen, LieSubalgebra.lieSpan_le]
        rintro _ (⟨i, rfl⟩ | ⟨i, rfl⟩)
        · exact ⟨serreE K b.affineCartanMatrixᵀ (some i), by simp⟩
        · exact ⟨serreF K b.affineCartanMatrixᵀ (some i), by simp⟩
      intro y
      have hy := hle (LieSubalgebra.mem_top y)
      rwa [LieSubalgebra.mem_comap, constHom_apply] at hy
    -- If degree `n` contains one nonzero mode in `R'`, simplicity of `L` gives all modes
    -- of degree `n`.
    have hdeg_of_ne : ∀ (n : ℤ) {v : L}, v ≠ 0 → mode Φ hΦ hΦs n v ∈ R' →
        ∀ y : L, mode Φ hΦ hΦs n y ∈ R' := by
      intro n v hv hvn
      let I_n : LieIdeal K L :=
        { carrier := {y : L | mode Φ hΦ hΦs n y ∈ R'}
          zero_mem' := by simp
          add_mem' := fun ha hb ↦ by
            change mode Φ hΦ hΦs n (_ + _) ∈ R'
            rw [map_add]
            exact add_mem ha hb
          smul_mem' := fun c _ ha ↦ by
            change mode Φ hΦ hΦs n (c • _) ∈ R'
            rw [map_smul]
            exact R'.smul_mem c ha
          lie_mem := fun {z y} hy ↦ by
            change mode Φ hΦ hΦs n ⁅z, y⁆ ∈ R'
            have hbra : ⁅mode Φ hΦ hΦs 0 z, mode Φ hΦ hΦs n y⁆ = mode Φ hΦ hΦs n ⁅z, y⁆ := by
              rw [lie_mode_mode, zero_add]
              split_ifs with hn
              · simp [hn]
              · simp
            rw [← hbra]
            exact R'.lie_mem (hconst z) hy }
      have hne : I_n ≠ ⊥ := by
        intro hbot
        have hv0 : v ∈ I_n := hvn
        rw [hbot, LieSubmodule.mem_bot] at hv0
        exact hv hv0
      have htop : I_n = ⊤ := (IsSimple.eq_bot_or_eq_top I_n).resolve_left hne
      intro y
      exact (htop.symm ▸ trivial : y ∈ I_n)
    have hθ_nz : b.highestRoot.1.IsNonZero := H.isNonZero_coe_root b.highestRoot
    have hcoroot_nz : (coroot b.highestRoot.1 : L) ≠ 0 := (hx.isSl2Triple _ hθ_nz).h_ne_zero
    have hpos1 : ∀ y : L, mode Φ hΦ hΦs 1 y ∈ R' :=
      hdeg_of_ne 1 (hx.ne_zero (-b.highestRoot.1) hθ_nz.neg)
        ⟨serreE K b.affineCartanMatrixᵀ none, by simp⟩
    have hneg1 : ∀ y : L, mode Φ hΦ hΦs (-1) y ∈ R' :=
      hdeg_of_ne (-1) (hx.ne_zero b.highestRoot.1 hθ_nz)
        ⟨serreF K b.affineCartanMatrixᵀ none, by simp⟩
    have hnat_pos : ∀ m : ℕ, ∀ y : L, mode Φ hΦ hΦs (m : ℤ) y ∈ R' := by
      intro m
      induction m with
      | zero => simpa using hconst
      | succ m ih =>
        rcases eq_or_ne m 0 with rfl | _
        · simpa using hpos1
        · refine hdeg_of_ne ((m + 1 : ℕ) : ℤ) hcoroot_nz ?_
          have hbra : ⁅mode Φ hΦ hΦs (m : ℤ) (x b.highestRoot.1),
              mode Φ hΦ hΦs 1 (x (-b.highestRoot.1))⁆ =
              mode Φ hΦ hΦs ((m + 1 : ℕ) : ℤ) (coroot b.highestRoot.1 : L) := by
            rw [lie_mode_mode_of_nonneg b (Int.natCast_nonneg m) zero_le_one,
              hx.lie_neg b.highestRoot.1 hθ_nz, Nat.cast_add, Nat.cast_one]
          rw [← hbra]
          exact R'.lie_mem (ih _) (hpos1 _)
    have hnat_neg : ∀ m : ℕ, ∀ y : L, mode Φ hΦ hΦs (-(m : ℤ)) y ∈ R' := by
      intro m
      induction m with
      | zero => simpa using hconst
      | succ m ih =>
        rcases eq_or_ne m 0 with rfl | _
        · simpa using hneg1
        · refine hdeg_of_ne (-((m + 1 : ℕ) : ℤ)) hcoroot_nz ?_
          have hbra : ⁅mode Φ hΦ hΦs (-(m : ℤ)) (x b.highestRoot.1),
              mode Φ hΦ hΦs (-1) (x (-b.highestRoot.1))⁆ =
              mode Φ hΦ hΦs (-((m + 1 : ℕ) : ℤ)) (coroot b.highestRoot.1 : L) := by
            rw [lie_mode_mode_of_nonpos b (by omega) (by norm_num),
              hx.lie_neg b.highestRoot.1 hθ_nz,
              show -(m : ℤ) + (-1) = -((m + 1 : ℕ) : ℤ) by push_cast; ring]
          rw [← hbra]
          exact R'.lie_mem (ih _) (hneg1 _)
    have hall : ∀ (n : ℤ) (y : L), mode Φ hΦ hΦs n y ∈ R' := fun n y ↦ by
      rcases Int.eq_nat_or_neg n with ⟨m, rfl | rfl⟩
      · exact hnat_pos m y
      · exact hnat_neg m y
    have hK : toExtendedResidueExtension Φ hΦ hΦs (centralElement c₀) ∈ R' := by
      obtain ⟨s, hs⟩ := affineCentralElement_mem_range_serreHom b
      change (serreHom b.affineRealization) s = _ at hs
      refine ⟨s, ?_⟩
      change affineLoopHom b hx (serreHom b.affineRealization s) = _
      rw [hs, affineLoopHom_centralElement]
    rintro _ ⟨u, rfl⟩
    obtain ⟨⟨p, z⟩, rfl⟩ := (ofProd c₀).surjective u
    rw [ofTwoCocycle.ofProd_eq_add_smul_centralElement, map_add, map_smul]
    refine add_mem ?_ (R'.smul_mem _ hK)
    obtain ⟨f, rfl⟩ := (toFinsupp K ℤ L).symm.surjective p
    induction f using Finsupp.induction_linear with
    | zero =>
      have h00 : ofProd c₀ (0, 0) = 0 := of_zero c₀
      rw [map_zero, h00, map_zero]
      exact zero_mem _
    | add f₁ f₂ h₁ h₂ =>
      have hadd : ofProd c₀ ((toFinsupp K ℤ L).symm f₁ + (toFinsupp K ℤ L).symm f₂, 0) =
          ofProd c₀ ((toFinsupp K ℤ L).symm f₁, 0) +
            ofProd c₀ ((toFinsupp K ℤ L).symm f₂, 0) := by
        simp [← of_add]
      rw [map_add, hadd, map_add]
      exact add_mem h₁ h₂
    | single n y =>
      rw [toFinsupp_symm_single]
      change toExtendedResidueExtension Φ hΦ hΦs
        (ofProd c₀ (AddMonoidAlgebra.single n 1 ⊗ₜ[K] y, 0)) ∈ R'
      rw [← mode_apply]
      exact hall n y

/-- **`affineLoopHom` is surjective.** -/
theorem affineLoopHom_surjective {x : Weight K H L → L} (hx : IsSl2System x) :
    Function.Surjective (affineLoopHom b hx) := by
  classical
  intro y
  obtain ⟨u, t, rfl⟩ := exists_eq_add_smul_degreeElement Φ hΦ hΦs y
  have hu : toExtendedResidueExtension Φ hΦ hΦs u ∈
      ((affineLoopHom b hx).comp (serreHom b.affineRealization)).range := by
    rw [range_affineLoopHom_comp_serreHom]
    exact ⟨u, rfl⟩
  obtain ⟨s, hs⟩ := hu
  refine ⟨serreHom b.affineRealization s + t • cartanElement b.affineRealization (0, 0, 1), ?_⟩
  rw [map_add, map_smul, affineLoopHom_degreeElement]
  exact congrArg (· + t • degreeElement Φ hΦ hΦs) hs

/-- The Cartan map `affineLoopCartan b` is injective on `H × K × K`. -/
private theorem affineLoopCartan_injective : Function.Injective (affineLoopCartan b) := by
  rw [injective_iff_map_eq_zero]
  rintro ⟨h, a, t⟩ hv
  have hprod := congrArg (extendedToProd Φ hΦ hΦs) hv
  rw [map_zero] at hprod
  have ht : t = 0 := by
    have h2 := congrArg Prod.snd hprod
    simpa [affineLoopCartan, mode_apply] using h2
  subst ht
  have hfst : ofProd c₀ (AddMonoidAlgebra.single (0 : ℤ) (1 : K) ⊗ₜ[K] (h : L), 0) +
      a • centralElement c₀ = 0 := by
    have h1 := congrArg Prod.fst hprod
    simpa [affineLoopCartan, mode_apply] using h1
  have hsymm := congrArg (ofProd c₀).symm hfst
  rw [of_symm_add, of_symm_smul, Equiv.symm_apply_apply, ofTwoCocycle.ofProd_symm_centralElement,
    of_symm_zero] at hsymm
  have ha : a = 0 := by
    have h2 := congrArg (fun q ↦ TrivialLieModule.equiv K (loopAlgebra K ℤ L) K q.2) hsymm
    simpa using h2
  subst ha
  have hh : h = 0 := by
    have hloop := congrArg (fun q ↦ toFinsupp K ℤ L q.1 0) hsymm
    simp only [zero_smul, add_zero] at hloop
    rw [← toFinsupp_symm_single, LinearEquiv.apply_symm_apply, Finsupp.single_eq_same] at hloop
    exact Subtype.ext hloop
  subst hh
  rfl

/-- Step A for injectivity: the kernel of `affineLoopHom` meets the Cartan subalgebra trivially. -/
private theorem ker_affineLoopHom_inf_cartan_eq_bot {x : Weight K H L → L} (hx : IsSl2System x) :
    (affineLoopHom b hx).ker.toSubmodule ⊓ LinearMap.range (cartanElement b.affineRealization) =
      ⊥ := by
  rw [eq_bot_iff]
  rintro u ⟨hker, v, rfl⟩
  rw [Submodule.mem_bot]
  have h0 : affineLoopCartan b v = 0 := by
    simpa [affineLoopHom] using LieHom.mem_ker.mp hker
  have hv0 : v = 0 := affineLoopCartan_injective b (by simpa using h0)
  rw [hv0, map_zero]

/-- For any realization of a generalized Cartan matrix (diagonal `2`) over a characteristic-zero
field, the derived subalgebra `𝔤' = (serreHom R).range` is perfect: `⁅⊤, ⊤⁆ = ⊤`. -/
private theorem derived_perfect_of_diag_two {ι H' : Type*} [DecidableEq ι]
    [AddCommGroup H'] [Module K H'] {A : Matrix ι ι ℤ}
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H') (hdiag : ∀ k, A k k = 2) :
    (⁅(⊤ : LieIdeal K (serreHom R).range), (⊤ : LieIdeal K (serreHom R).range)⁆ :
      LieIdeal K (serreHom R).range) = ⊤ := by
  refine eq_top_iff.mpr fun w _ ↦ ?_
  suffices ∀ u : PresentedLieAlgebra R, (hu : u ∈ (serreHom R).range) →
      (⟨u, hu⟩ : (serreHom R).range) ∈
        (⁅(⊤ : LieIdeal K (serreHom R).range), (⊤ : LieIdeal K (serreHom R).range)⁆ :
          LieIdeal K (serreHom R).range) from
    this w.1 w.2
  intro u hu
  have hu' : u ∈ LieSubalgebra.lieSpan K (PresentedLieAlgebra R)
      (Set.range (positiveGenerator R) ∪ Set.range (negativeGenerator R)) := by
    rw [← range_serreHom]
    exact hu
  induction hu' using LieSubalgebra.lieSpan_induction with
  | mem v hv =>
    rcases hv with ⟨k, rfl⟩ | ⟨k, rfl⟩
    · have hh : cartanElement R (R.coroot k) ∈ (serreHom R).range :=
        ⟨serreH K A k, serreHom_serreH R k⟩
      have heq : (⟨positiveGenerator R k, hu⟩ : (serreHom R).range) =
          (2 : K)⁻¹ • ⁅(⟨cartanElement R (R.coroot k), hh⟩ : (serreHom R).range),
            ⟨positiveGenerator R k, hu⟩⁆ := by
        apply Subtype.ext
        change positiveGenerator R k =
          (2 : K)⁻¹ • ⁅cartanElement R (R.coroot k), positiveGenerator R k⁆
        rw [lie_cartanElement_positiveGenerator, R.root_coroot, Matrix.map_apply, hdiag k,
          Int.cast_ofNat, smul_smul, inv_mul_cancel₀ two_ne_zero, one_smul]
      rw [heq]
      exact Submodule.smul_mem _ _
        (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _))
    · have hh : cartanElement R (R.coroot k) ∈ (serreHom R).range :=
        ⟨serreH K A k, serreHom_serreH R k⟩
      have heq : (⟨negativeGenerator R k, hu⟩ : (serreHom R).range) =
          (-(2 : K)⁻¹) • ⁅(⟨cartanElement R (R.coroot k), hh⟩ : (serreHom R).range),
            ⟨negativeGenerator R k, hu⟩⁆ := by
        apply Subtype.ext
        change negativeGenerator R k =
          (-(2 : K)⁻¹) • ⁅cartanElement R (R.coroot k), negativeGenerator R k⁆
        rw [lie_cartanElement_negativeGenerator, R.root_coroot, Matrix.map_apply, hdiag k,
          Int.cast_ofNat, smul_neg, neg_smul, neg_neg, smul_smul, inv_mul_cancel₀ two_ne_zero,
          one_smul]
      rw [heq]
      exact Submodule.smul_mem _ _
        (LieSubmodule.lie_mem_lie (LieSubmodule.mem_top _) (LieSubmodule.mem_top _))
  | zero => exact zero_mem _
  | add a b ha hb iha ihb =>
    have ha' : a ∈ (serreHom R).range := by rwa [range_serreHom]
    have hb' : b ∈ (serreHom R).range := by rwa [range_serreHom]
    exact add_mem (iha ha') (ihb hb')
  | smul c a ha iha =>
    have ha' : a ∈ (serreHom R).range := by rwa [range_serreHom]
    exact Submodule.smul_mem _ c (iha ha')
  | lie a b ha hb _ _ =>
    have ha' : a ∈ (serreHom R).range := by rwa [range_serreHom]
    have hb' : b ∈ (serreHom R).range := by rwa [range_serreHom]
    exact LieSubmodule.lie_mem_lie (x := (⟨a, ha'⟩ : (serreHom R).range))
      (m := (⟨b, hb'⟩ : (serreHom R).range)) (LieSubmodule.mem_top _) (LieSubmodule.mem_top _)

/-- The degree component of `affineLoopHom` vanishes on the derived subalgebra `𝔤'`. -/
private theorem extendedToProd_snd_affineLoopHom_of_mem_derived [DecidableEq (Option b.support)]
    {x : Weight K H L → L} (hx : IsSl2System x)
    (y : (serreHom b.affineRealization).range) :
    (extendedToProd Φ hΦ hΦs (affineLoopHom b hx y.1)).2 = 0 := by
  obtain ⟨s, hs⟩ := y.2
  have hmem : affineLoopHom b hx y.1 ∈ (toExtendedResidueExtension Φ hΦ hΦs).range := by
    rw [← range_affineLoopHom_comp_serreHom b hx]
    exact ⟨s, congrArg (affineLoopHom b hx) hs⟩
  obtain ⟨u, hu⟩ := hmem
  change toExtendedResidueExtension Φ hΦ hΦs u = affineLoopHom b hx y.1 at hu
  rw [← hu, extendedToProd_toExtendedResidueExtension]

/-- The restriction of `affineLoopHom` to the derived subalgebra `𝔤'`, valued in the central
extension `ĝ = ofTwoCocycle c₀`. -/
private def affineLoopDerivedHom [DecidableEq (Option b.support)]
    {x : Weight K H L → L} (hx : IsSl2System x) :
    (serreHom b.affineRealization).range →ₗ⁅K⁆ ofTwoCocycle c₀ where
  toFun y := (extendedToProd Φ hΦ hΦs (affineLoopHom b hx y.1)).1
  map_add' y₁ y₂ := by simp
  map_smul' r y := by simp
  map_lie' {y₁ y₂} := by
    have hto (y : (serreHom b.affineRealization).range) :
        toExtendedResidueExtension Φ hΦ hΦs
          (extendedToProd Φ hΦ hΦs (affineLoopHom b hx y.1)).1 = affineLoopHom b hx y.1 := by
      apply (extendedToProd Φ hΦ hΦs).injective
      rw [extendedToProd_toExtendedResidueExtension]
      exact Prod.ext rfl (extendedToProd_snd_affineLoopHom_of_mem_derived b hx y).symm
    apply toExtendedResidueExtension_injective Φ hΦ hΦs
    rw [LieHom.map_lie, hto, hto, hto, ← LieHom.map_lie]
    rfl

private theorem toExtendedResidueExtension_affineLoopDerivedHom [DecidableEq (Option b.support)]
    {x : Weight K H L → L} (hx : IsSl2System x) (y : (serreHom b.affineRealization).range) :
    toExtendedResidueExtension Φ hΦ hΦs (affineLoopDerivedHom b hx y) = affineLoopHom b hx y.1 := by
  apply (extendedToProd Φ hΦ hΦs).injective
  rw [extendedToProd_toExtendedResidueExtension]
  exact Prod.ext rfl (extendedToProd_snd_affineLoopHom_of_mem_derived b hx y).symm

private theorem proj_affineLoopDerivedHom_eq_of_eq_mode [DecidableEq (Option b.support)]
    {x : Weight K H L → L} (hx : IsSl2System x)
    (y : (serreHom b.affineRealization).range) (n : ℤ) (v : L)
    (hy : affineLoopHom b hx y.1 = mode Φ hΦ hΦs n v) :
    ofTwoCocycle.proj c₀ (affineLoopDerivedHom b hx y) =
      AddMonoidAlgebra.single n (1 : K) ⊗ₜ[K] v := by
  have h : affineLoopDerivedHom b hx y =
      ofProd c₀ (AddMonoidAlgebra.single n (1 : K) ⊗ₜ[K] v, 0) := by
    apply toExtendedResidueExtension_injective Φ hΦ hΦs
    rw [toExtendedResidueExtension_affineLoopDerivedHom, hy, mode_apply]
  rw [h, ofTwoCocycle.proj_apply, Equiv.symm_apply_apply]

omit [CharZero K] in
/-- For any realization `R`, a linear combination `c = ∑ k, w k • R.coroot k` lying in the derived
subalgebra equals `∑ k, w k • ⁅eₖ, fₖ⁆` inside `(serreHom R).range`. -/
private theorem cartanElement_sum_coroot_eq_sum_lie {ι H' : Type*} [Fintype ι] [DecidableEq ι]
    [AddCommGroup H'] [Module K H'] {A : Matrix ι ι ℤ}
    (R : CartanRealization (A.map (Int.cast : ℤ → K)) H')
    (w : ι → K) (c : H') (hc : c = ∑ k, w k • R.coroot k)
    (hc_mem : cartanElement R c ∈ (serreHom R).range) :
    (⟨cartanElement R c, hc_mem⟩ : (serreHom R).range) =
      ∑ k : ι, w k •
        ⁅(⟨positiveGenerator R k, ⟨serreE K A k, serreHom_serreE R k⟩⟩ : (serreHom R).range),
          ⟨negativeGenerator R k, ⟨serreF K A k, serreHom_serreF R k⟩⟩⁆ := by
  apply Subtype.ext
  change (serreHom R).range.incl ⟨cartanElement R c, hc_mem⟩ = (serreHom R).range.incl _
  rw [map_sum]
  change cartanElement R c = _
  rw [hc, map_sum]
  refine Finset.sum_congr rfl fun k _ ↦ ?_
  rw [map_smul, map_smul, LieHom.map_lie]
  exact congrArg _ (lie_positiveGenerator_negativeGenerator_self R k).symm

/-- Every `L`-invariant bilinear form on `L` is a scalar multiple of `affineResidueForm b`. -/
private theorem exists_eq_smul_affineResidueForm (Ψ : LinearMap.BilinForm K L)
    (hΨ : Ψ.lieInvariant L) : ∃ t : K, Ψ = t • affineResidueForm b := by
  obtain ⟨r, hr⟩ := TauCeti.LieAlgebra.IsKilling.exists_eq_smul_killingForm_of_isSimple H hΨ
  refine ⟨-(r * (2 * (b.dualCoxeterNumber : K))), ?_⟩
  have hh : (2 * (b.dualCoxeterNumber : K)) ≠ 0 :=
    mul_ne_zero two_ne_zero (b.cast_dualCoxeterNumber_ne_zero (R := K))
  ext u v
  simp only [hr, affineResidueForm, normalizedKillingForm, LinearMap.smul_apply,
    LinearMap.neg_apply, smul_eq_mul, neg_mul, mul_neg, neg_neg]
  rw [← mul_assoc, mul_assoc r, mul_inv_cancel₀ hh, mul_one]

/-- `affineLoopDerivedHom` is surjective onto the central extension `ofTwoCocycle c₀`. -/
private theorem affineLoopDerivedHom_surjective [DecidableEq (Option b.support)]
    {x : Weight K H L → L} (hx : IsSl2System x) :
    Function.Surjective (affineLoopDerivedHom b hx) := by
  intro u
  have hu : toExtendedResidueExtension Φ hΦ hΦs u ∈
      ((affineLoopHom b hx).comp (serreHom b.affineRealization)).range := by
    rw [range_affineLoopHom_comp_serreHom b hx]
    exact ⟨u, rfl⟩
  obtain ⟨s, hs⟩ := hu
  refine ⟨⟨serreHom b.affineRealization s, ⟨s, rfl⟩⟩, ?_⟩
  apply toExtendedResidueExtension_injective Φ hΦ hΦs
  rw [toExtendedResidueExtension_affineLoopDerivedHom]
  exact hs

/-- The nonvanishing residue-pairing condition on Chevalley generators for
`lie_top_ker_eq_ker_of_surjective_ofTwoCocycle`. -/
private theorem affineLoopDerivedHom_residuePairing_ne_zero [DecidableEq (Option b.support)]
    {x : Weight K H L → L} (hx : IsSl2System x) :
    ∑ k : Option b.support,
      (b.affineComarks k : K) * residuePairing K ℤ L Φ
        (ofTwoCocycle.proj c₀ (affineLoopDerivedHom b hx
          ⟨positiveGenerator b.affineRealization k,
            ⟨serreE K b.affineCartanMatrixᵀ k, serreHom_serreE _ k⟩⟩))
        (ofTwoCocycle.proj c₀ (affineLoopDerivedHom b hx
          ⟨negativeGenerator b.affineRealization k,
            ⟨serreF K b.affineCartanMatrixᵀ k, serreHom_serreF _ k⟩⟩)) ≠ 0 := by
  rw [Fintype.sum_option]
  have hsome (i : b.support) :
      residuePairing K ℤ L Φ
        (ofTwoCocycle.proj c₀ (affineLoopDerivedHom b hx
          ⟨positiveGenerator b.affineRealization (some i),
            ⟨serreE K b.affineCartanMatrixᵀ (some i), serreHom_serreE _ (some i)⟩⟩))
        (ofTwoCocycle.proj c₀ (affineLoopDerivedHom b hx
          ⟨negativeGenerator b.affineRealization (some i),
            ⟨serreF K b.affineCartanMatrixᵀ (some i), serreHom_serreF _ (some i)⟩⟩)) = 0 := by
    rw [proj_affineLoopDerivedHom_eq_of_eq_mode b hx _ 0 (x i.1.1)
        (affineLoopHom_positiveGenerator_some b hx i),
      proj_affineLoopDerivedHom_eq_of_eq_mode b hx _ 0 (x (-i.1.1))
        (affineLoopHom_negativeGenerator_some b hx i),
      residuePairing_single_tmul]
    simp
  have hnone :
      residuePairing K ℤ L Φ
        (ofTwoCocycle.proj c₀ (affineLoopDerivedHom b hx
          ⟨positiveGenerator b.affineRealization none,
            ⟨serreE K b.affineCartanMatrixᵀ none, serreHom_serreE _ none⟩⟩))
        (ofTwoCocycle.proj c₀ (affineLoopDerivedHom b hx
          ⟨negativeGenerator b.affineRealization none,
            ⟨serreF K b.affineCartanMatrixᵀ none, serreHom_serreF _ none⟩⟩)) = 1 := by
    rw [proj_affineLoopDerivedHom_eq_of_eq_mode b hx _ 1 (x (-b.highestRoot.1))
        (affineLoopHom_positiveGenerator_none b hx),
      proj_affineLoopDerivedHom_eq_of_eq_mode b hx _ (-1) (x b.highestRoot.1)
        (affineLoopHom_negativeGenerator_none b hx),
      residuePairing_single_tmul]
    simp [affineResidueForm, normalizedKillingForm_neg_highestRoot b hx]
  simp only [hsome, mul_zero, Finset.sum_const_zero, add_zero, b.affineComarks_none,
    Int.cast_one, one_mul, hnone]
  exact one_ne_zero

/-- Step B for injectivity: for `I' = comap g'.incl (affineLoopHom b hx).ker`, we have
`⁅⊤, I'⁆ = I'`, by universal central extensions of `loopAlgebra K ℤ L`. -/
private theorem lie_top_ker_affineLoopHom_derived [DecidableEq (Option b.support)]
    {x : Weight K H L → L} (hx : IsSl2System x) :
    ⁅(⊤ : LieIdeal K (serreHom b.affineRealization).range),
      LieIdeal.comap (serreHom b.affineRealization).range.incl (affineLoopHom b hx).ker⁆ =
      LieIdeal.comap (serreHom b.affineRealization).range.incl (affineLoopHom b hx).ker := by
  have hker_eq : (affineLoopDerivedHom b hx).ker =
      LieIdeal.comap (serreHom b.affineRealization).range.incl (affineLoopHom b hx).ker := by
    ext y
    rw [LieHom.mem_ker]
    change affineLoopDerivedHom b hx y = 0 ↔ affineLoopHom b hx y.1 = 0
    rw [← toExtendedResidueExtension_affineLoopDerivedHom b hx y]
    exact ⟨fun h ↦ by simp [h],
      fun h ↦ toExtendedResidueExtension_injective Φ hΦ hΦs (by simpa using h)⟩
  let c_g' : (serreHom b.affineRealization).range :=
    ⟨cartanElement b.affineRealization b.affineCentralElement,
      affineCentralElement_mem_range_serreHom b⟩
  have hc_cent (y : (serreHom b.affineRealization).range) : ⁅y, c_g'⁆ = 0 := Subtype.ext <| by
    change ⁅y.1, cartanElement b.affineRealization b.affineCentralElement⁆ = 0
    rw [← lie_skew, lie_affineCentralElement, neg_zero]
  have hf'_c : affineLoopDerivedHom b hx c_g' = centralElement c₀ := by
    apply toExtendedResidueExtension_injective Φ hΦ hΦs
    rw [toExtendedResidueExtension_affineLoopDerivedHom]
    exact affineLoopHom_centralElement b hx
  have hmain :
      ⁅(⊤ : LieIdeal K (serreHom b.affineRealization).range), (affineLoopDerivedHom b hx).ker⁆ =
        (affineLoopDerivedHom b hx).ker :=
    lie_top_ker_eq_ker_of_surjective_ofTwoCocycle hΦ hΦs
      (exists_eq_smul_affineResidueForm b)
      (affineLoopDerivedHom_surjective b hx)
      (derived_perfect_of_diag_two b.affineRealization
        fun k ↦ by rw [Matrix.transpose_apply, b.affineCartanMatrix_apply_same])
      hc_cent hf'_c
      (cartanElement_sum_coroot_eq_sum_lie b.affineRealization
        (fun k ↦ (b.affineComarks k : K)) b.affineCentralElement b.affineCentralElement_def
        (affineCentralElement_mem_range_serreHom b))
      (affineLoopDerivedHom_residuePairing_ne_zero b hx)
  exact ((congrArg (Bracket.bracket (⊤ : LieIdeal K (serreHom b.affineRealization).range))
    hker_eq.symm).trans hmain).trans hker_eq

/-- **`affineLoopHom` is injective.** -/
theorem affineLoopHom_injective {x : Weight K H L → L} (hx : IsSl2System x) :
    Function.Injective (affineLoopHom b hx) := by
  classical
  rw [← LieHom.ker_eq_bot]
  refine lieIdeal_eq_bot_of_disjoint_cartan_of_derived_eq_self b.affineRealization
    (fun k ↦ by simp)
    (ker_affineLoopHom_inf_cartan_eq_bot b hx)
    (lie_top_ker_affineLoopHom_derived b hx)
    b.affineComarks_pos
    (fun u _ ↦ ?_)
  rw [← b.affineCentralElement_def]
  exact lie_affineCentralElement b u

/-- **Kac's Theorem 7.4**: the untwisted affine Kac–Moody algebra
`PresentedLieAlgebra b.affineRealization` is isomorphic to the extended affine loop algebra
`extendedResidueExtension (affineResidueForm b) ... = (K[t, t⁻¹] ⊗ L ⊕ K K) ⋊ K d`. -/
def affineLoopEquiv {x : Weight K H L → L} (hx : IsSl2System x) :
    PresentedLieAlgebra b.affineRealization ≃ₗ⁅K⁆ E' :=
  LieEquiv.ofBijective (affineLoopHom b hx)
    ⟨affineLoopHom_injective b hx, affineLoopHom_surjective b hx⟩

/-- The Cartan realization embeds injectively into `PresentedLieAlgebra b.affineRealization`. -/
theorem cartanElement_affineRealization_injective :
    Function.Injective (cartanElement b.affineRealization) := by
  obtain ⟨x, hx⟩ := TauCeti.exists_isSl2System K H (L := L)
  intro u v huv
  apply affineLoopCartan_injective b
  have h := congrArg (affineLoopHom b hx) huv
  simpa [affineLoopHom] using h

@[simp]
theorem affineLoopEquiv_cartanElement {x : Weight K H L → L} (hx : IsSl2System x)
    (h : H) (a t : K) :
    affineLoopEquiv b hx (cartanElement b.affineRealization (h, a, t)) =
      mode Φ hΦ hΦs 0 (h : L) +
        a • toExtendedResidueExtension Φ hΦ hΦs (centralElement c₀) +
        t • degreeElement Φ hΦ hΦs :=
  affineLoopHom_cartanElement b hx h a t

/-- `affineLoopEquiv` sends the canonical central element `c` to the central element `K`. -/
theorem affineLoopEquiv_centralElement {x : Weight K H L → L} (hx : IsSl2System x) :
    affineLoopEquiv b hx (cartanElement b.affineRealization b.affineCentralElement) =
      toExtendedResidueExtension Φ hΦ hΦs (centralElement c₀) :=
  affineLoopHom_centralElement b hx

/-- `affineLoopEquiv` sends the scaling element `d = (0, 0, 1)` to `degreeElement`. -/
theorem affineLoopEquiv_degreeElement {x : Weight K H L → L} (hx : IsSl2System x) :
    affineLoopEquiv b hx (cartanElement b.affineRealization (0, 0, 1)) =
      degreeElement Φ hΦ hΦs :=
  affineLoopHom_degreeElement b hx

@[simp]
theorem affineLoopEquiv_positiveGenerator_none {x : Weight K H L → L} (hx : IsSl2System x) :
    affineLoopEquiv b hx (positiveGenerator b.affineRealization none) =
      mode Φ hΦ hΦs 1 (x (-b.highestRoot.1)) :=
  affineLoopHom_positiveGenerator_none b hx

@[simp]
theorem affineLoopEquiv_positiveGenerator_some {x : Weight K H L → L} (hx : IsSl2System x)
    (i : b.support) :
    affineLoopEquiv b hx (positiveGenerator b.affineRealization (some i)) =
      mode Φ hΦ hΦs 0 (x i.1.1) :=
  affineLoopHom_positiveGenerator_some b hx i

@[simp]
theorem affineLoopEquiv_negativeGenerator_none {x : Weight K H L → L} (hx : IsSl2System x) :
    affineLoopEquiv b hx (negativeGenerator b.affineRealization none) =
      mode Φ hΦ hΦs (-1) (x b.highestRoot.1) :=
  affineLoopHom_negativeGenerator_none b hx

@[simp]
theorem affineLoopEquiv_negativeGenerator_some {x : Weight K H L → L} (hx : IsSl2System x)
    (i : b.support) :
    affineLoopEquiv b hx (negativeGenerator b.affineRealization (some i)) =
      mode Φ hΦ hΦs 0 (x (-i.1.1)) :=
  affineLoopHom_negativeGenerator_some b hx i

/-! ### The standard invariant bilinear form on the untwisted affine Kac–Moody algebra -/

/-- **The standard nondegenerate symmetric invariant bilinear form** on the untwisted affine
Kac–Moody algebra `PresentedLieAlgebra b.affineRealization`, pulled back from `extendedBilinForm`
along `affineLoopEquiv b hx`. -/
def affineInvariantForm {x : Weight K H L → L} (hx : IsSl2System x) :
    LinearMap.BilinForm K (PresentedLieAlgebra b.affineRealization) :=
  (extendedBilinForm Φ hΦ hΦs).compl₁₂
    (affineLoopEquiv b hx).toLinearEquiv.toLinearMap
    (affineLoopEquiv b hx).toLinearEquiv.toLinearMap

theorem affineInvariantForm_apply {x : Weight K H L → L} (hx : IsSl2System x)
    (u v : PresentedLieAlgebra b.affineRealization) :
    affineInvariantForm b hx u v =
      extendedBilinForm Φ hΦ hΦs (affineLoopEquiv b hx u) (affineLoopEquiv b hx v) :=
  (rfl)

/-- `affineInvariantForm` is symmetric. -/
theorem affineInvariantForm_isSymm {x : Weight K H L → L} (hx : IsSl2System x) :
    (affineInvariantForm b hx).IsSymm :=
  LinearMap.BilinForm.isSymm_def.mpr fun u v ↦
    (extendedBilinForm_isSymm Φ hΦ hΦs).eq (affineLoopEquiv b hx u) (affineLoopEquiv b hx v)

/-- `affineInvariantForm` is invariant under the adjoint action. -/
theorem affineInvariantForm_lieInvariant {x : Weight K H L → L} (hx : IsSl2System x) :
    (affineInvariantForm b hx).lieInvariant (PresentedLieAlgebra b.affineRealization) :=
  fun u v w ↦ by
    simp only [affineInvariantForm_apply, LieEquiv.map_lie]
    exact extendedBilinForm_lieInvariant Φ hΦ hΦs
      (affineLoopEquiv b hx u) (affineLoopEquiv b hx v) (affineLoopEquiv b hx w)

/-- `affineInvariantForm` is nondegenerate. -/
theorem affineInvariantForm_nondegenerate {x : Weight K H L → L} (hx : IsSl2System x) :
    (affineInvariantForm b hx).Nondegenerate := by
  have hnd := extendedBilinForm_nondegenerate Φ hΦ hΦs (affineResidueForm_nondegenerate b)
  refine ⟨fun u hu ↦ (affineLoopEquiv b hx).injective ?_,
    fun v hv ↦ (affineLoopEquiv b hx).injective ?_⟩
  · rw [map_zero]
    refine hnd.1 _ fun y ↦ ?_
    obtain ⟨w, rfl⟩ := (affineLoopEquiv b hx).surjective y
    exact hu w
  · rw [map_zero]
    refine hnd.2 _ fun y ↦ ?_
    obtain ⟨w, rfl⟩ := (affineLoopEquiv b hx).surjective y
    exact hv w

/-- On the Cartan subalgebra, `affineInvariantForm` is `κ₀(h₁, h₂) + a₁ t₂ + t₁ a₂`. -/
@[simp]
theorem affineInvariantForm_cartanElement {x : Weight K H L → L} (hx : IsSl2System x)
    (h₁ h₂ : H) (a₁ a₂ t₁ t₂ : K) :
    affineInvariantForm b hx
        (cartanElement b.affineRealization (h₁, a₁, t₁))
        (cartanElement b.affineRealization (h₂, a₂, t₂)) =
      normalizedKillingForm b (h₁ : L) (h₂ : L) + a₁ * t₂ + t₁ * a₂ := by
  rw [affineInvariantForm_apply, affineLoopEquiv_cartanElement, affineLoopEquiv_cartanElement]
  simp only [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, smul_eq_mul,
    extendedBilinForm_mode_mode, extendedBilinForm_mode_centralElement,
    extendedBilinForm_centralElement_mode, extendedBilinForm_mode_degreeElement,
    extendedBilinForm_degreeElement_mode, extendedBilinForm_centralElement_centralElement,
    extendedBilinForm_degreeElement_degreeElement,
    extendedBilinForm_centralElement_degreeElement,
    extendedBilinForm_degreeElement_centralElement, add_zero, ↓reduceIte]
  have hΦh : Φ (h₁ : L) (h₂ : L) = -normalizedKillingForm b (h₁ : L) (h₂ : L) := rfl
  rw [hΦh]
  ring

/-- Pairing the affine coroot `h₀` with `(h, a, t)` gives `α₀(h, a, t) = t - θ(h)`. -/
theorem affineInvariantForm_coroot_none_cartanElement {x : Weight K H L → L} (hx : IsSl2System x)
    (h : H) (a t : K) :
    affineInvariantForm b hx
        (cartanElement b.affineRealization (b.affineRealization.coroot none))
        (cartanElement b.affineRealization (h, a, t)) =
      b.affineRealization.root none (h, a, t) := by
  rw [b.affineRealization_coroot_none, affineInvariantForm_cartanElement, NegMemClass.coe_neg,
    map_neg, LinearMap.neg_apply, normalizedKillingForm_coroot_highestRoot_apply,
    b.affineRealization_root_none, rootSystem_toLinearMap_apply]
  ring

/-- Pairing a finite simple coroot `hᵢ` with `(h, a, t)` gives
`(aᵢ / aᵢ^∨) * αᵢ(h, a, t)`. -/
theorem affineInvariantForm_coroot_some_cartanElement {x : Weight K H L → L} (hx : IsSl2System x)
    (i : b.support) (h : H) (a t : K) :
    affineInvariantForm b hx
        (cartanElement b.affineRealization (b.affineRealization.coroot (some i)))
        (cartanElement b.affineRealization (h, a, t)) =
      ((b.affineMarks (some i) : K) / (b.affineComarks (some i) : K)) *
        b.affineRealization.root (some i) (h, a, t) := by
  rw [b.affineRealization_coroot_some, affineInvariantForm_cartanElement,
    normalizedKillingForm_coroot_simple_apply, b.affineRealization_root_some,
    rootSystem_toLinearMap_apply]
  ring

/-- `(c, d) = 1` under `affineInvariantForm`. -/
theorem affineInvariantForm_centralElement_degreeElement {x : Weight K H L → L}
    (hx : IsSl2System x) :
    affineInvariantForm b hx
      (cartanElement b.affineRealization b.affineCentralElement)
      (cartanElement b.affineRealization (0, 0, 1)) = 1 := by
  rw [affineInvariantForm_apply, affineLoopEquiv_centralElement, affineLoopEquiv_degreeElement,
    extendedBilinForm_centralElement_degreeElement]

/-- `(c, c) = 0` under `affineInvariantForm`. -/
theorem affineInvariantForm_centralElement_centralElement {x : Weight K H L → L}
    (hx : IsSl2System x) :
    affineInvariantForm b hx
      (cartanElement b.affineRealization b.affineCentralElement)
      (cartanElement b.affineRealization b.affineCentralElement) = 0 := by
  rw [affineInvariantForm_apply, affineLoopEquiv_centralElement,
    extendedBilinForm_centralElement_centralElement]

/-- `(d, d) = 0` under `affineInvariantForm`. -/
theorem affineInvariantForm_degreeElement_degreeElement {x : Weight K H L → L}
    (hx : IsSl2System x) :
    affineInvariantForm b hx
      (cartanElement b.affineRealization (0, 0, 1))
      (cartanElement b.affineRealization (0, 0, 1)) = 0 := by
  rw [affineInvariantForm_apply, affineLoopEquiv_degreeElement,
    extendedBilinForm_degreeElement_degreeElement]

/-- `(e₀, f₀) = 1` under `affineInvariantForm`. -/
@[simp]
theorem affineInvariantForm_positiveGenerator_negativeGenerator_none {x : Weight K H L → L}
    (hx : IsSl2System x) :
    affineInvariantForm b hx
      (positiveGenerator b.affineRealization none)
      (negativeGenerator b.affineRealization none) = 1 := by
  rw [affineInvariantForm_apply, affineLoopEquiv_positiveGenerator_none,
    affineLoopEquiv_negativeGenerator_none, extendedBilinForm_mode_mode]
  simp [affineResidueForm, normalizedKillingForm_neg_highestRoot b hx]

/-- `(eᵢ, fᵢ) = aᵢ / aᵢ^∨` under `affineInvariantForm`. -/
theorem affineInvariantForm_positiveGenerator_negativeGenerator_some {x : Weight K H L → L}
    (hx : IsSl2System x) (i : b.support) :
    affineInvariantForm b hx
      (positiveGenerator b.affineRealization (some i))
      (negativeGenerator b.affineRealization (some i)) =
      (b.affineMarks (some i) : K) / (b.affineComarks (some i) : K) := by
  rw [affineInvariantForm_apply, affineLoopEquiv_positiveGenerator_some,
    affineLoopEquiv_negativeGenerator_some, extendedBilinForm_mode_mode]
  simp [affineResidueForm, normalizedKillingForm_simple_neg b hx i]

/-- Distinct Chevalley generators `eₖ` and `fₗ` (`k ≠ l`) are orthogonal under
`affineInvariantForm`. -/
theorem affineInvariantForm_positiveGenerator_negativeGenerator_of_ne {x : Weight K H L → L}
    (hx : IsSl2System x) {k l : Option b.support} (hkl : k ≠ l) :
    affineInvariantForm b hx
      (positiveGenerator b.affineRealization k)
      (negativeGenerator b.affineRealization l) = 0 := by
  rcases k with _ | i <;> rcases l with _ | j
  · exact absurd rfl hkl
  · rw [affineInvariantForm_apply, affineLoopEquiv_positiveGenerator_none,
      affineLoopEquiv_negativeGenerator_some, extendedBilinForm_mode_mode]
    simp
  · rw [affineInvariantForm_apply, affineLoopEquiv_positiveGenerator_some,
      affineLoopEquiv_negativeGenerator_none, extendedBilinForm_mode_mode]
    simp
  · have hij : i ≠ j := fun h ↦ hkl (congrArg some h)
    rw [affineInvariantForm_apply, affineLoopEquiv_positiveGenerator_some,
      affineLoopEquiv_negativeGenerator_some, extendedBilinForm_mode_mode]
    have hadd : (⇑i.1.1 : H → K) + ⇑(-j.1.1) ≠ 0 := by
      intro h0
      have hEq : (i.1.1 : H → K) = (j.1.1 : H → K) := by
        funext h
        have hh := congrFun h0 h
        simp only [Pi.add_apply, Weight.coe_neg, Pi.neg_apply, Pi.zero_apply] at hh
        linear_combination hh
      exact hij (Subtype.ext (Subtype.ext (Weight.ext (congrFun hEq))))
    have hkill : killingForm K L (x i.1.1) (x (-j.1.1)) = 0 :=
      LieAlgebra.killingForm_apply_eq_zero_of_mem_rootSpace_of_add_ne_zero K L H
        (hx.mem_rootSpace i.1.1) (hx.mem_rootSpace (-j.1.1)) hadd
    simp [affineResidueForm, normalizedKillingForm, hkill]

/-! ### Level transport to any nonzero multiple of the normalized invariant form -/

/-- **Kac's isomorphism at arbitrary nonzero level**: for any invariant symmetric form
`Ψ = u • affineResidueForm b` (`u : Kˣ`), `PresentedLieAlgebra b.affineRealization` is isomorphic
to `extendedResidueExtension Ψ hΨ hΨs`, sending `c ↦ u • K`, `d ↦ d`, and fixing all loop modes
of the generators. -/
def affineLoopEquivOfUnit {x : Weight K H L → L} (hx : IsSl2System x)
    {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    {u : Kˣ} (hu : Ψ = (u : K) • Φ) :
    PresentedLieAlgebra b.affineRealization ≃ₗ⁅K⁆ extendedResidueExtension Ψ hΨ hΨs :=
  (affineLoopEquiv b hx).trans (extendedLevelEquiv hΦ hΦs hΨ hΨs hu)

/-- `affineLoopEquivOfUnit` sends `c` to `u • K`. -/
theorem affineLoopEquivOfUnit_centralElement {x : Weight K H L → L} (hx : IsSl2System x)
    {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    {u : Kˣ} (hu : Ψ = (u : K) • Φ) :
    affineLoopEquivOfUnit b hx hΨ hΨs hu
        (cartanElement b.affineRealization b.affineCentralElement) =
      (u : K) • toExtendedResidueExtension Ψ hΨ hΨs
        (centralElement (twoCocycleOfBilinear K ℤ L Ψ hΨ hΨs)) := by
  rw [affineLoopEquivOfUnit, LieEquiv.trans_apply, affineLoopEquiv_centralElement,
    extendedLevelEquiv_centralElement]

/-- `affineLoopEquivOfUnit` preserves the degree element `d = (0, 0, 1)`. -/
@[simp]
theorem affineLoopEquivOfUnit_degreeElement {x : Weight K H L → L} (hx : IsSl2System x)
    {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    {u : Kˣ} (hu : Ψ = (u : K) • Φ) :
    affineLoopEquivOfUnit b hx hΨ hΨs hu (cartanElement b.affineRealization (0, 0, 1)) =
      degreeElement Ψ hΨ hΨs := by
  rw [affineLoopEquivOfUnit, LieEquiv.trans_apply, affineLoopEquiv_degreeElement,
    extendedLevelEquiv_degreeElement]

/-- Under `affineLoopEquivOfUnit`, `extendedBilinForm Ψ` pulls back to `u * affineInvariantForm`. -/
theorem extendedBilinForm_affineLoopEquivOfUnit {x : Weight K H L → L} (hx : IsSl2System x)
    {Ψ : LinearMap.BilinForm K L} (hΨ : Ψ.lieInvariant L) (hΨs : Ψ.IsSymm)
    {u : Kˣ} (hu : Ψ = (u : K) • Φ)
    (v w : PresentedLieAlgebra b.affineRealization) :
    extendedBilinForm Ψ hΨ hΨs
        (affineLoopEquivOfUnit b hx hΨ hΨs hu v)
        (affineLoopEquivOfUnit b hx hΨ hΨs hu w) =
      (u : K) * affineInvariantForm b hx v w :=
  extendedBilinForm_extendedLevelEquiv hΦ hΦs hΨ hΨs hu
    (affineLoopEquiv b hx v) (affineLoopEquiv b hx w)

end AffineLoop

end TauCeti.KacMoody
