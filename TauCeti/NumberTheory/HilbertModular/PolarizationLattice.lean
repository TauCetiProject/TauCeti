/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.BilinearForm.DualLattice
public import Mathlib.LinearAlgebra.Matrix.ToLin
public import Mathlib.NumberTheory.NumberField.FractionalIdeal
public import Mathlib.RingTheory.DedekindDomain.Different
public import Mathlib.RingTheory.Spectrum.Prime.FreeLocus
public import TauCeti.RingTheory.Trace.WedgeForm
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import TauCeti.RingTheory.DedekindDomain.Different.Basic
import TauCeti.RingTheory.FractionalIdeal.Projective

/-!
# The polarization lattices of Hilbert modular varieties

Let `K` be a number field with ring of integers `𝓞 K` and inverse different
`𝔡⁻¹ = FractionalIdeal.dual ℤ ℚ 1`. For a fractional ideal `c` of `𝓞 K`, the polarization lattice
is the `𝓞 K`-submodule of row vectors

```text
L_c = 𝓞_K ⊕ c⁻¹𝔡⁻¹ ⊆ K².
```

For a totally real `K` and a nonzero ideal `c` it is the integral lattice of the Hilbert modular
Shimura datum with `c`-polarization, refining its rational representation on `K²`. The integral
alternating forms on it are the restrictions of the trace symplectic forms
`ψ_a(x, y) = Tr_{K/ℚ}(a (x₀ y₁ - x₁ y₀))` of `TauCeti.traceWedgeForm` with parameter `a ∈ c`,
an `𝓞 K`-module family of `ℤ`-valued forms rather than a single principal form. The lattice is
defined without choosing a generator of `c`, so nonprincipal polarization modules are included.
Its `ℤ`-dual for `ψ₁` is `c ⊕ 𝔡⁻¹ = c L_c`, which determines the level groups stabilizing it.

## Main definitions

* `TauCeti.HilbertModular.polarizationLattice c`: the lattice `L_c = 𝓞_K ⊕ c⁻¹𝔡⁻¹`.
* `TauCeti.HilbertModular.polarizationLatticeEquivProd c`: `L_c` is the product of its two
  coordinate fractional ideals.
* `TauCeti.HilbertModular.integralTraceWedgeForm c`: the `ℤ`-linear family `a ↦ ψ_{c, a}` of
  alternating `ℤ`-valued `ℤ`-bilinear forms on `L_c`, indexed by `a ∈ c`.

## Main statements

* `TauCeti.HilbertModular.mem_polarizationLattice`: `x ∈ L_c ↔ x₀ ∈ 𝓞_K ∧ x₁ ∈ c⁻¹𝔡⁻¹`.
* `TauCeti.HilbertModular.projective_polarizationLattice`,
  `TauCeti.HilbertModular.rankAtStalk_polarizationLattice`: `L_c` is finite projective over
  `𝓞 K`, of rank two at every prime for `c ≠ 0`.
* `TauCeti.HilbertModular.finrank_int_polarizationLattice`: for `c ≠ 0`, `L_c` is free of rank
  `2 [K : ℚ]` over `ℤ`.
* `TauCeti.HilbertModular.map_polarizationLattice`: the row action of `diag(1, a⁻¹)` carries
  `L_c` onto `L_{a c}` as an equality of submodules.
* `TauCeti.HilbertModular.exists_traceWedgeForm_eq_intCast`: for `a ∈ c` the trace symplectic
  form `ψ_a` is integral on `L_c`.
* `TauCeti.HilbertModular.mem_dualSubmodule_polarizationLattice`: for `c ≠ 0` the `ℤ`-dual of
  `L_c` for `ψ₁` is `c ⊕ 𝔡⁻¹`.

## References

* C. Birkbeck, B. Heuer and C. Williams, *Overconvergent Hilbert modular forms via perfectoid
  modular varieties*, Ann. Inst. Fourier 73 (2023), Notation 5.1(3) and Definition 5.2(1).
* P. Deligne and G. Pappas, *Singularités des espaces de modules de Hilbert, en les
  caractéristiques divisant le discriminant*, Compositio Math. 90 (1994), §2.
-/

public section

open Module NumberField FractionalIdeal
open scoped Matrix nonZeroDivisors

namespace TauCeti.HilbertModular

variable {K : Type*} [Field K] [NumberField K]

/-- The polarization lattice `L_c = 𝓞_K ⊕ c⁻¹𝔡⁻¹` of row vectors in `K²`, for a fractional ideal
`c` of `𝓞 K`, where `𝔡⁻¹ = FractionalIdeal.dual ℤ ℚ 1` is the inverse different. -/
noncomputable def polarizationLattice (c : FractionalIdeal (𝓞 K)⁰ K) :
    Submodule (𝓞 K) (Fin 2 → K) :=
  Submodule.pi Set.univ
    ![((1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K),
      ((c⁻¹ * dual ℤ ℚ 1 : FractionalIdeal (𝓞 K)⁰ K) : Submodule (𝓞 K) K)]

@[simp]
theorem mem_polarizationLattice {c : FractionalIdeal (𝓞 K)⁰ K} {x : Fin 2 → K} :
    x ∈ polarizationLattice c ↔ x 0 ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) ∧
      x 1 ∈ c⁻¹ * dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  simp only [polarizationLattice, Submodule.mem_pi, Set.mem_univ, true_implies,
    Fin.forall_fin_two, Matrix.cons_val_zero, Matrix.cons_val_one, mem_coeToSubmodule]

/-- For `c ≠ 0`, the second coordinate ideal `c⁻¹𝔡⁻¹` of `L_c` is nonzero. -/
private theorem inv_mul_dual_one_ne_zero {c : FractionalIdeal (𝓞 K)⁰ K} (hc : c ≠ 0) :
    c⁻¹ * dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) ≠ 0 :=
  mul_ne_zero (inv_ne_zero hc) (dual_ne_zero ℤ ℚ one_ne_zero)

/-- For `c ≠ 0`, `u ∈ c` and `v ∈ c⁻¹𝔡⁻¹`, the product `u v` lies in `𝔡⁻¹`. -/
private theorem mul_mem_dual_one_of_mem_inv_mul {c : FractionalIdeal (𝓞 K)⁰ K} (hc : c ≠ 0)
    {u v : K} (hu : u ∈ c) (hv : v ∈ c⁻¹ * dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
    u * v ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  simpa only [mul_inv_cancel_left₀ hc] using mul_mem_mul hu hv

/-- The polarization lattice `L_c` is the product of the fractional ideals `𝓞_K` and `c⁻¹𝔡⁻¹`
of its two coordinates. -/
noncomputable def polarizationLatticeEquivProd (c : FractionalIdeal (𝓞 K)⁰ K) :
    polarizationLattice c ≃ₗ[𝓞 K]
      (1 : FractionalIdeal (𝓞 K)⁰ K) × (c⁻¹ * dual ℤ ℚ 1 : FractionalIdeal (𝓞 K)⁰ K) where
  toFun x :=
    (⟨x.val 0, (mem_polarizationLattice.1 x.property).1⟩,
      ⟨x.val 1, (mem_polarizationLattice.1 x.property).2⟩)
  invFun y := ⟨![y.1, y.2], mem_polarizationLattice.2 ⟨y.1.property, y.2.property⟩⟩
  map_add' _ _ := rfl
  map_smul' _ _ := rfl
  left_inv _ := Subtype.ext <| funext <| Fin.forall_fin_two.2 ⟨rfl, rfl⟩
  right_inv _ := rfl

@[simp]
theorem coe_polarizationLatticeEquivProd_apply_fst (c : FractionalIdeal (𝓞 K)⁰ K)
    (x : polarizationLattice c) : ((polarizationLatticeEquivProd c x).1 : K) = x.val 0 :=
  (rfl)

@[simp]
theorem coe_polarizationLatticeEquivProd_apply_snd (c : FractionalIdeal (𝓞 K)⁰ K)
    (x : polarizationLattice c) : ((polarizationLatticeEquivProd c x).2 : K) = x.val 1 :=
  (rfl)

@[simp]
theorem coe_polarizationLatticeEquivProd_symm_apply (c : FractionalIdeal (𝓞 K)⁰ K)
    (y : (1 : FractionalIdeal (𝓞 K)⁰ K) × (c⁻¹ * dual ℤ ℚ 1 : FractionalIdeal (𝓞 K)⁰ K)) :
    ((polarizationLatticeEquivProd c).symm y : Fin 2 → K) = ![(y.1 : K), (y.2 : K)] :=
  (rfl)

instance (c : FractionalIdeal (𝓞 K)⁰ K) : Module.Free ℤ (polarizationLattice c) :=
  Module.Free.of_equiv ((polarizationLatticeEquivProd c).restrictScalars ℤ).symm

instance (c : FractionalIdeal (𝓞 K)⁰ K) : Module.Finite ℤ (polarizationLattice c) :=
  Module.Finite.equiv ((polarizationLatticeEquivProd c).restrictScalars ℤ).symm

instance (c : FractionalIdeal (𝓞 K)⁰ K) : Module.Finite (𝓞 K) (polarizationLattice c) :=
  Module.Finite.of_restrictScalars_finite ℤ _ _

/-- For `c ≠ 0`, the polarization lattice `L_c` is free of rank `2 [K : ℚ]` over `ℤ`. -/
theorem finrank_int_polarizationLattice {c : FractionalIdeal (𝓞 K)⁰ K} (hc : c ≠ 0) :
    finrank ℤ (polarizationLattice c) = 2 * finrank ℚ K := by
  have h₀ := fractionalIdeal_rank K (1 : (FractionalIdeal (𝓞 K)⁰ K)ˣ)
  have h₁ := fractionalIdeal_rank K (Units.mk0 _ (inv_mul_dual_one_ne_zero hc))
  rw [Units.val_one] at h₀
  rw [Units.val_mk0] at h₁
  rw [((polarizationLatticeEquivProd c).restrictScalars ℤ).finrank_eq, finrank_prod, h₀, h₁,
    RingOfIntegers.rank, two_mul]

/-- The polarization lattice `L_c` is a projective `𝓞 K`-module. -/
instance projective_polarizationLattice (c : FractionalIdeal (𝓞 K)⁰ K) :
    Module.Projective (𝓞 K) (polarizationLattice c) :=
  Module.Projective.of_equiv (polarizationLatticeEquivProd c).symm

/-- For `c ≠ 0`, the polarization lattice `L_c` has rank two over `𝓞 K`. -/
theorem finrank_polarizationLattice {c : FractionalIdeal (𝓞 K)⁰ K} (hc : c ≠ 0) :
    finrank (𝓞 K) (polarizationLattice c) = 2 := by
  -- `L_c` spans `K²`, of rank two over `𝓞 K`; it contains `(1, 0)` and `(0, d)` for some
  -- nonzero `d ∈ c⁻¹𝔡⁻¹`, which are linearly independent.
  obtain ⟨d, hd, hd0⟩ : ∃ d ∈ c⁻¹ * dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K), d ≠ 0 := by
    by_contra! h
    exact inv_mul_dual_one_ne_zero hc (eq_zero_iff.2 h)
  apply finrank_eq_of_rank_eq
  apply le_antisymm
  · grw [Submodule.rank_le, ← IsFractionRing.rank_right_eq (𝓞 K) K, rank_fin_fun]
  · let v : Fin 2 → polarizationLattice c :=
      ![⟨![1, 0], mem_polarizationLattice.2 ⟨one_mem_one _, zero_mem _⟩⟩,
        ⟨![0, d], mem_polarizationLattice.2 ⟨zero_mem _, hd⟩⟩]
    have hv : LinearIndependent (𝓞 K) v := by
      refine LinearIndependent.of_comp (polarizationLattice c).subtype ?_
      refine Fintype.linearIndependent_iff.2 fun g hg ↦ ?_
      have h₀ : (g 0 : K) = 0 := by simpa [v, Fin.sum_univ_two] using congr_fun hg 0
      have h₁ : (g 1 : K) * d = 0 := by simpa [v, Fin.sum_univ_two] using congr_fun hg 1
      intro i
      fin_cases i
      · exact_mod_cast h₀
      · exact_mod_cast (mul_eq_zero.1 h₁).resolve_right hd0
    simpa using hv.cardinal_lift_le_rank

/-- For `c ≠ 0`, the polarization lattice has rank two at every prime of `𝓞 K`. -/
theorem rankAtStalk_polarizationLattice {c : FractionalIdeal (𝓞 K)⁰ K} (hc : c ≠ 0)
    (p : PrimeSpectrum (𝓞 K)) : Module.rankAtStalk (polarizationLattice c) p = 2 := by
  rw [Module.rankAtStalk_eq, p.asIdeal.finrank_fiber_eq_finrank, finrank_polarizationLattice hc]

/-- A row vector `x` lies in `L_c` exactly when `x diag(1, a⁻¹)` lies in `L_{a c}`: the row
action of `diag(1, a⁻¹)` carries the polarization lattice `L_c` onto `L_{a c}`. -/
theorem vecMul_diagonal_mem_polarizationLattice_iff {a : K} (ha : a ≠ 0)
    {c : FractionalIdeal (𝓞 K)⁰ K} {x : Fin 2 → K} :
    x ᵥ* Matrix.diagonal ![1, a⁻¹] ∈ polarizationLattice (spanSingleton (𝓞 K)⁰ a * c) ↔
      x ∈ polarizationLattice c := by
  simp only [mem_polarizationLattice, Matrix.vecMul_diagonal, Matrix.cons_val_zero,
    Matrix.cons_val_one, mul_one, mul_inv, spanSingleton_inv, mul_assoc, mem_singleton_mul]
  refine and_congr_right fun _ ↦ ⟨fun ⟨y, hy, h⟩ ↦ ?_, fun h ↦ ⟨x 1, h, mul_comm _ _⟩⟩
  rw [mul_comm, mul_right_inj' (inv_ne_zero ha)] at h
  rwa [h]

/-- The image of `L_c` under the right row action of `diag(1, a⁻¹)` is the polarization lattice
of the rescaled ideal `(a)c`. -/
theorem map_polarizationLattice {a : K} (ha : a ≠ 0) (c : FractionalIdeal (𝓞 K)⁰ K) :
    (polarizationLattice c).map ((Matrix.diagonal ![1, a⁻¹]).vecMulLinear.restrictScalars (𝓞 K)) =
      polarizationLattice (spanSingleton (𝓞 K)⁰ a * c) := by
  let f := (Matrix.diagonal ![1, a⁻¹]).vecMulLinear.restrictScalars (𝓞 K)
  have hf : Function.Surjective f := by
    apply Matrix.vecMul_surjective_iff_isUnit.mpr
    rw [Matrix.isUnit_diagonal, Pi.isUnit_iff, Fin.forall_fin_two]
    simp [ha]
  change (polarizationLattice c).map f = _
  have hcomap : (polarizationLattice (spanSingleton (𝓞 K)⁰ a * c)).comap f =
      polarizationLattice c :=
    Submodule.ext fun _ ↦ vecMul_diagonal_mem_polarizationLattice_iff ha
  rw [← hcomap, Submodule.map_comap_eq_of_surjective hf]

/-- For `a ∈ c` and `x, y ∈ L_c`, the wedge `a (x₀ y₁ - x₁ y₀)` lies in `𝔡⁻¹`. -/
private theorem mul_wedge_mem_dual_one {c : FractionalIdeal (𝓞 K)⁰ K} {a : K} (ha : a ∈ c)
    {x y : Fin 2 → K} (hx : x ∈ polarizationLattice c) (hy : y ∈ polarizationLattice c) :
    a * (x 0 * y 1 - x 1 * y 0) ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  obtain ⟨hx₀, hx₁⟩ := mem_polarizationLattice.1 hx
  obtain ⟨hy₀, hy₁⟩ := mem_polarizationLattice.1 hy
  rcases eq_or_ne c 0 with rfl | hc
  · rw [(mem_zero_iff _).1 ha, zero_mul]
    exact zero_mem _
  have h {u v : K} (hu : u ∈ (1 : FractionalIdeal (𝓞 K)⁰ K))
      (hv : v ∈ c⁻¹ * dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) :
      u * (a * v) ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    simpa only [one_mul] using mul_mem_mul hu (mul_mem_dual_one_of_mem_inv_mul hc ha hv)
  rw [← mem_coeToSubmodule]
  convert Submodule.sub_mem _ (h hx₀ hy₁) (h hy₀ hx₁) using 1
  ring

/-- For `a ∈ c`, the trace symplectic form `ψ_a` takes integer values on the polarization
lattice `L_c`. -/
theorem exists_traceWedgeForm_eq_intCast {c : FractionalIdeal (𝓞 K)⁰ K} {a : K} (ha : a ∈ c)
    {x y : Fin 2 → K} (hx : x ∈ polarizationLattice c) (hy : y ∈ polarizationLattice c) :
    ∃ n : ℤ, traceWedgeForm ℚ a x y = n := by
  obtain ⟨n, hn⟩ := trace_mem_range_of_mem_dual_one (mul_wedge_mem_dual_one ha hx hy)
  exact ⟨n, by rw [traceWedgeForm_apply, ← hn, algebraMap_int_eq, eq_intCast]⟩

/-- The restriction of the trace symplectic form `ψ_a` to `L_c`, for `a ∈ c`, as a `ℤ`-valued
form. It is the value at `a` of `integralTraceWedgeForm c`. -/
private noncomputable def integralTraceWedgeFormAux (c : FractionalIdeal (𝓞 K)⁰ K)
    (a : (c : Submodule (𝓞 K) K)) :
    LinearMap.BilinForm ℤ (polarizationLattice c) :=
  LinearMap.codRestrict₂
    (((traceWedgeForm ℚ (a : K)).restrictScalars₁₂ ℤ ℤ).compl₁₂
      ((polarizationLattice c).subtype.restrictScalars ℤ)
      ((polarizationLattice c).subtype.restrictScalars ℤ))
    (Int.castAddHom ℚ).toIntLinearMap Int.cast_injective fun x y ↦ by
      obtain ⟨n, hn⟩ := exists_traceWedgeForm_eq_intCast a.property x.property y.property
      exact ⟨n, by simp [hn]⟩

private theorem intCast_integralTraceWedgeFormAux_apply (c : FractionalIdeal (𝓞 K)⁰ K)
    (a : (c : Submodule (𝓞 K) K)) (x y : polarizationLattice c) :
    ((integralTraceWedgeFormAux c a x y : ℤ) : ℚ) = traceWedgeForm ℚ (a : K) x y := by
  unfold integralTraceWedgeFormAux
  exact LinearMap.codRestrict₂_apply (i := (Int.castAddHom ℚ).toIntLinearMap)
    (hi := Int.cast_injective) _ _ x y

/-- The integral trace polarization forms on `L_c`: the `ℤ`-linear family `a ↦ ψ_{c, a}` indexed
by `a ∈ c`, where `ψ_{c, a}` is the restriction of the trace symplectic form `ψ_a` to `L_c`, an
alternating `ℤ`-bilinear form with values in `ℤ` (`intCast_integralTraceWedgeForm_apply`). -/
noncomputable def integralTraceWedgeForm (c : FractionalIdeal (𝓞 K)⁰ K) :
    (c : Submodule (𝓞 K) K) →ₗ[ℤ] LinearMap.BilinForm ℤ (polarizationLattice c) where
  toFun := integralTraceWedgeFormAux c
  map_add' a b := LinearMap.ext₂ fun x y ↦ Int.cast_injective (α := ℚ) <| by
    simp [intCast_integralTraceWedgeFormAux_apply]
  map_smul' n a := LinearMap.ext₂ fun x y ↦ Int.cast_injective (α := ℚ) <| by
    simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, eq_intCast,
      intCast_integralTraceWedgeFormAux_apply, Submodule.coe_smul_of_tower, map_zsmul]
    exact (zsmul_eq_mul _ _).symm

variable {c : FractionalIdeal (𝓞 K)⁰ K}

@[simp]
theorem intCast_integralTraceWedgeForm_apply (a : (c : Submodule (𝓞 K) K))
    (x y : polarizationLattice c) :
    ((integralTraceWedgeForm c a x y : ℤ) : ℚ) = traceWedgeForm ℚ (a : K) x y :=
  intCast_integralTraceWedgeFormAux_apply c a x y

@[simp]
theorem integralTraceWedgeForm_self (a : (c : Submodule (𝓞 K) K)) (x : polarizationLattice c) :
    integralTraceWedgeForm c a x x = 0 :=
  Int.cast_injective (α := ℚ) <| by
    rw [intCast_integralTraceWedgeForm_apply, traceWedgeForm_self, Int.cast_zero]

theorem isAlt_integralTraceWedgeForm (a : (c : Submodule (𝓞 K) K)) :
    (integralTraceWedgeForm c a).IsAlt :=
  integralTraceWedgeForm_self a

/-- The parameter of `ψ_c` can be moved into the first argument:
`ψ_{c, b a}(x, y) = ψ_{c, a}(b x, y)` for `b ∈ 𝓞 K`. -/
theorem integralTraceWedgeForm_smul_left (b : 𝓞 K) (a : (c : Submodule (𝓞 K) K))
    (x y : polarizationLattice c) :
    integralTraceWedgeForm c (b • a) x y = integralTraceWedgeForm c a (b • x) y :=
  Int.cast_injective (α := ℚ) <| by
    rw [intCast_integralTraceWedgeForm_apply, intCast_integralTraceWedgeForm_apply,
      Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def, ← algebraMap_smul K b]
    exact traceWedgeForm_mul_smul_left _ _ _ _

/-- The parameter of `ψ_c` can be moved into the second argument:
`ψ_{c, b a}(x, y) = ψ_{c, a}(x, b y)` for `b ∈ 𝓞 K`. -/
theorem integralTraceWedgeForm_smul_right (b : 𝓞 K) (a : (c : Submodule (𝓞 K) K))
    (x y : polarizationLattice c) :
    integralTraceWedgeForm c (b • a) x y = integralTraceWedgeForm c a x (b • y) :=
  Int.cast_injective (α := ℚ) <| by
    rw [intCast_integralTraceWedgeForm_apply, intCast_integralTraceWedgeForm_apply,
      Submodule.coe_smul, Submodule.coe_smul, Algebra.smul_def, ← algebraMap_smul K b]
    exact traceWedgeForm_mul_smul_right _ _ _ _

/-- For `c ≠ 0`, the `ℤ`-dual of the polarization lattice `L_c = 𝓞_K ⊕ c⁻¹𝔡⁻¹` for the trace
symplectic form `ψ₁` is `c ⊕ 𝔡⁻¹`. -/
theorem mem_dualSubmodule_polarizationLattice (hc : c ≠ 0) {x : Fin 2 → K} :
    x ∈ (traceWedgeForm ℚ (1 : K)).dualSubmodule ((polarizationLattice c).restrictScalars ℤ) ↔
      x 0 ∈ c ∧ x 1 ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
  rw [LinearMap.BilinForm.mem_dualSubmodule]
  refine ⟨fun h ↦ ⟨?_, ?_⟩, fun ⟨h₀, h₁⟩ y hy ↦ ?_⟩
  · -- Testing against `(0, t)` for `t ∈ c⁻¹𝔡⁻¹` puts `x₀` in the trace dual of `c⁻¹𝔡⁻¹`.
    have hdual : dual ℤ ℚ (c⁻¹ * dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K)) = c := by
      rw [dual_eq_mul_inv, mul_inv, inv_inv, mul_left_comm,
        mul_inv_cancel₀ (dual_ne_zero ℤ ℚ one_ne_zero), mul_one]
    rw [← hdual, mem_dual (inv_mul_dual_one_ne_zero hc)]
    intro t ht
    have := h ![0, t] (mem_polarizationLattice.2 ⟨zero_mem _, ht⟩)
    simpa [traceWedgeForm_apply, Submodule.mem_one] using this
  · -- Testing against `(-t, 0)` for `t ∈ 𝓞_K` puts `x₁` in `𝔡⁻¹`.
    rw [mem_dual one_ne_zero]
    intro t ht
    have := h ![-t, 0] (mem_polarizationLattice.2 ⟨Submodule.neg_mem _ ht, zero_mem _⟩)
    simpa [traceWedgeForm_apply, Submodule.mem_one] using this
  · obtain ⟨hy₀, hy₁⟩ := mem_polarizationLattice.1 hy
    have h : x 0 * y 1 - x 1 * y 0 ∈ dual ℤ ℚ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
      have h₁ := mul_mem_mul h₁ hy₀
      rw [mul_one] at h₁
      exact Submodule.sub_mem _ (mul_mem_dual_one_of_mem_inv_mul hc h₀ hy₁) h₁
    obtain ⟨n, hn⟩ := trace_mem_range_of_mem_dual_one h
    exact Submodule.mem_one.2 ⟨n, by simp [traceWedgeForm_apply, ← hn]⟩

-- Over `ℚ`, the row `(0, 1/2)` belongs to the lattice for `(2)` but not the lattice for `(1)`.
example :
    ![0, (1 / 2 : ℚ)] ∈ polarizationLattice (spanSingleton (𝓞 ℚ)⁰ (2 : ℚ)) ∧
      ![0, (1 / 2 : ℚ)] ∉ polarizationLattice (K := ℚ) 1 := by
  refine ⟨?_, ?_⟩
  · have h : ![0, (1 : ℚ)] ∈ polarizationLattice (K := ℚ) 1 := by
      rw [mem_polarizationLattice, inv_one, one_mul]
      exact ⟨zero_mem _, one_le_dual_one ℤ ℚ (one_mem_one _)⟩
    have h₂ := (vecMul_diagonal_mem_polarizationLattice_iff (a := (2 : ℚ)) (by norm_num)).mpr h
    have hrow : ![0, (1 : ℚ)] ᵥ* Matrix.diagonal ![1, (2 : ℚ)⁻¹] = ![0, (1 / 2 : ℚ)] := by
      ext i
      fin_cases i <;> simp [Matrix.vecMul_diagonal, one_div]
    simpa only [hrow, mul_one] using h₂
  · rw [mem_polarizationLattice, inv_one, one_mul]
    rintro ⟨_, h⟩
    rcases trace_mem_range_of_mem_dual_one h with ⟨n, hn⟩
    have hn' : (n : ℚ) = 1 / 2 := by simpa [algebraMap_int_eq] using hn
    have hn₂ : (n : ℚ) * 2 = 1 := (eq_div_iff (by norm_num)).mp hn'
    exact (by omega : ¬ n * 2 = 1) (by exact_mod_cast hn₂)

end TauCeti.HilbertModular
