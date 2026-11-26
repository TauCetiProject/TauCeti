/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.Geometry.Symplectic.Floer.Cap.Orbit
public import TauCeti.Geometry.Symplectic.Hamiltonian.ConstantOrbit.ConleyZehnder.Manifold
import TauCeti.Geometry.Symplectic.ExistsCompatible
import TauCeti.Geometry.Symplectic.Hamiltonian.PeriodicOrbit

/-!
# The grading of constant capped orbits

A constant one-periodic orbit `x` of a time-dependent vector field, sitting at a zero `p` of the
field, is capped by the constant disc at `p`. Its cap class with the orientation of discs is
`TauCeti.Floer.OrbitCapClass.const`, the class of the constant smooth based cap
(`TauCeti.Floer.isSmoothBasedCap_orbitLoop_const`). Along the constant disc the tangent bundle is
framed by the identity of `T_p M`, so for the Hamiltonian vector fields of a symplectic form `σ`
the Conley–Zehnder index of the capped orbit `⟨x, const⟩` is the Conley–Zehnder index of the path
`t ↦ dφ_{0,t}(p)` of linear symplectic maps of the single symplectic vector space `(T_p M, σ_p)`
(`TauCeti.Floer.CappedOrbit.conleyZehnderIndex_const`), by
`TauCeti.Floer.IsSmoothBasedCap.conleyZehnderIndex_const`.

This fixes the normalization of the grading `μ` of capped Hamiltonian Floer theory on a closed
symplectic manifold `(M, σ)` of dimension `2 n`. Let `F` be a Morse function on `M`. For small
`ε > 0` every contractible one-periodic orbit of the autonomous Hamiltonian `ε F` is the constant
orbit at a critical point `p` of `F`, and the capped orbit `⟨p, const⟩` has the grading

`μ(p, const) = ind_p(F) - n`

(`TauCeti.Floer.CappedOrbit.exists_pos_forall_grading_const_eq_manifoldMorseIndex_sub`), by the
computation of the linearized flow at a nondegenerate critical point
(`exists_pos_forall_conleyZehnderIndex_eq_manifoldMorseIndex_sub` in the namespace
`TauCeti.SmoothTwoForm.IsNondegenerate`).
So the maximum of `F` has grading `n` and the minimum grading `-n`. With the recapping law
`μ(B +ᵥ q) = μ(q) + 2 c₁(B)` (`TauCeti.Floer.CappedOrbit.grading_vadd`) this determines the grading
of every capped orbit of `ε F`: the generator `⟨p, B +ᵥ const⟩` has grading
`ind_p(F) - n + 2 c₁(B)`.

The grading is Tau Ceti's coordinate-free Conley–Zehnder index, read in bases in which the
symplectic form has the matrix `J`; this is the opposite sign to the index in the complex
coordinates of `ℂⁿ`, in which the same grading is written `μ = -CZ`.

## Main definitions

* `TauCeti.Floer.OrbitCapClass.const`: the cap class of the constant disc of a constant orbit.

## Main results

* `TauCeti.Floer.isSmoothBasedCap_orbitLoop_const`: the constant disc is a smooth based cap of the
  loop of a constant orbit.
* `TauCeti.Floer.OrbitCapClass.toSphericalCapClass_const`: its cap class.
* `TauCeti.Floer.CappedOrbit.conleyZehnderIndex_const`: the Conley–Zehnder index of a constant
  orbit capped by the constant disc is that of its linearized flow on one tangent space.
* `TauCeti.Floer.CappedOrbit.exists_pos_forall_grading_const_eq_manifoldMorseIndex_sub`:
  the normalization `μ = ind_p(F) - n` at the constant orbits of a small Morse Hamiltonian.

## References

* D. Salamon, *Lectures on Floer homology*, in *Symplectic geometry and topology*, IAS/Park City
  Math. Ser. **7**, AMS, 1999, Lecture 2 (the Conley–Zehnder index of the constant orbits of a
  small Morse function).
* D. McDuff and D. Salamon, *J-holomorphic Curves and Symplectic Topology*, 2nd ed., AMS (2012),
  Section 12.1 (the grading of capped periodic orbits and its normalization).
-/

public section

noncomputable section

open Set Module AlgebraicTopology HomotopyGroup
-- `ω` names the area homomorphism here, so the `ContDiff` scope, whose notation includes `ω`, is
-- not opened, and smoothness `∞` is written out.
open scoped Manifold Topology

namespace TauCeti.Floer

variable {E H : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [TopologicalSpace H]
  {I : ModelWithCorners ℝ E H} {M : Type} [TopologicalSpace M] [ChartedSpace H M]
  {X : ℝ → (x : M) → TangentSpace I x}

/-- **The constant cap of a constant orbit.** If a contractible `1`-periodic solution `x` stays at
`x 0`, the constant map at `x 0` is a smooth based cap of its loop. -/
theorem isSmoothBasedCap_orbitLoop_const {x : contractiblePeriodicSolutions X 1}
    (hx : ∀ t, x.val t = x.val 0) : IsSmoothBasedCap I (orbitLoop x) fun _ ↦ x.val 0 :=
  ⟨contMDiff_const, fun _ ↦ rfl, fun t ↦ ((orbitLoop_apply x t).trans (hx t)).symm, fun _ ↦ rfl,
    fun _ ↦ rfl⟩

variable (ω : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℝ)
  (c : ((singularHomologyFunctor (ModuleCat.{0} ℤ) 2).obj (ModuleCat.of ℤ ℤ)).obj
    (TopCat.of M) →+ ℤ)

/-- The **constant cap class** of a contractible `1`-periodic solution `x` that stays at `x 0`: the
cap class of the constant disc at `x 0` (`TauCeti.Floer.isSmoothBasedCap_orbitLoop_const`). -/
def OrbitCapClass.const {x : contractiblePeriodicSolutions X 1} (hx : ∀ t, x.val t = x.val 0) :
    OrbitCapClass ω c x :=
  OrbitCapClass.toSphericalCapClass.symm
    (SphericalCapClass.mk ω c (isSmoothBasedCap_orbitLoop_const hx).homotopyClass)

/-- The defining equation of `TauCeti.Floer.OrbitCapClass.const`. -/
theorem OrbitCapClass.const_def {x : contractiblePeriodicSolutions X 1}
    (hx : ∀ t, x.val t = x.val 0) :
    OrbitCapClass.const ω c hx = OrbitCapClass.toSphericalCapClass.symm
      (SphericalCapClass.mk ω c (isSmoothBasedCap_orbitLoop_const hx).homotopyClass) :=
  (rfl)

/-- The constant cap class of a constant orbit is the class of the raw cap of the constant disc. -/
@[simp]
theorem OrbitCapClass.toSphericalCapClass_const {x : contractiblePeriodicSolutions X 1}
    (hx : ∀ t, x.val t = x.val 0) :
    OrbitCapClass.toSphericalCapClass (OrbitCapClass.const ω c hx) =
      SphericalCapClass.mk ω c (isSmoothBasedCap_orbitLoop_const hx).homotopyClass := by
  rw [OrbitCapClass.const_def, Equiv.apply_symm_apply]

namespace CappedOrbit

variable {ω c} [FiniteDimensional ℝ E] [I.Boundaryless] [IsManifold I ((⊤ : ℕ∞) : WithTop ℕ∞) M]
  [T2Space M] [SigmaCompactSpace M] {σ : SmoothTwoForm I M} (hσ : σ.IsSymplectic)
  (hc : ∀ y a, c (hurewiczIntHom M y 1 a) = hσ.isNondegenerate.firstChernHom y a)

/-- **The index of a constant capped orbit.** Let `x` be a contractible `1`-periodic orbit of the
Hamiltonian vector fields `X t` of `Ham t` that stays at the point `p = x 0`. The Conley–Zehnder
index of `x` capped by the constant disc is the Conley–Zehnder index of the path `t ↦ dφ_{0,t}(p)`,
`t ∈ [0, 1]`, of linear symplectic maps of `(T_p M, σ_p)`, read on the model space `E` of `T_p M`
as any path `Ψ` with `Ψ(t) = dφ_{0,t}(p)`. -/
theorem conleyZehnderIndex_const
    (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
      (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
    {Ham : ℝ → M → ℝ} (hXH : ∀ t, σ.IsHamiltonianVectorField (Ham t) (X t))
    (hHam : ∀ t, ContMDiff I 𝓘(ℝ) 2 (Ham t)) {x : contractiblePeriodicSolutions X 1}
    (hx : ∀ t, x.val t = x.val 0) {A B : E →L[ℝ] E} (Ψ : Path A B)
    (hΨ : ∀ t v w, hσ.isNondegenerate.symplecticFormAt (x.val 0) (Ψ t v) (Ψ t w) =
      hσ.isNondegenerate.symplecticFormAt (x.val 0) v w)
    (hΨt : ∀ t : unitInterval, Ψ t = mfderiv I I (timeDependentFlowOf X 0 t) (x.val 0)) :
    conleyZehnderIndex hX hσ hXH hHam hc ⟨x, OrbitCapClass.const ω c hx⟩ =
      SymplecticForm.conleyZehnderIndex (V := E)
        (hσ.isNondegenerate.symplecticFormAt (x.val 0)) Ψ hΨ := by
  rw [OrbitCapClass.const_def, conleyZehnderIndex_mk_homotopyClass]
  exact IsSmoothBasedCap.conleyZehnderIndex_const hσ.isNondegenerate _ _ _ Ψ hΨ fun t v ↦
    (DFunLike.congr_fun (hΨt t) v).trans (orbitLinearizedFlow_apply _ x t v).symm

/-- **The normalization of the grading.** Let `σ` be a symplectic form on a compact boundaryless
manifold `M` of dimension `2 n`, and `F` a Morse function on `M`. There is `ε₀ > 0` such that for
`0 < ε ≤ ε₀` and Hamiltonian vector fields `X t` of the autonomous Hamiltonian `Ham t = ε F`, every
contractible `1`-periodic orbit `x` of `X` stays at a critical point `p = x 0` of `F`, and `x`
capped by the constant disc has the grading `ind_p(F) - n`. -/
theorem exists_pos_forall_grading_const_eq_manifoldMorseIndex_sub [CompactSpace M] {F : M → ℝ}
    (hF : IsMorse I F) :
    ∃ ε₀ > (0 : ℝ), ∀ ε, 0 < ε → ε ≤ ε₀ →
      ∀ {X : ℝ → (x : M) → TangentSpace I x}
        (hX : ContMDiff (𝓘(ℝ, ℝ).prod I) I.tangent ((⊤ : ℕ∞) : WithTop ℕ∞)
          (fun p : ℝ × M ↦ (⟨p.2, X p.1 p.2⟩ : TangentBundle I M)))
        {Ham : ℝ → M → ℝ} (hXH : ∀ t, σ.IsHamiltonianVectorField (Ham t) (X t))
        (hHam : ∀ t, ContMDiff I 𝓘(ℝ) 2 (Ham t)), (∀ t, Ham t = ε • F) →
        ∀ x : contractiblePeriodicSolutions X 1, ∃ hx : ∀ t, x.val t = x.val 0,
          x.val 0 ∈ criticalPoints I F ∧
            grading hX hσ hXH hHam hc ⟨x, OrbitCapClass.const ω c hx⟩ =
              (manifoldMorseIndex I F (x.val 0) : ℤ) - (finrank ℝ E / 2 : ℕ) := by
  have h := hσ.isNondegenerate
  have hF3 : ContMDiff I 𝓘(ℝ) 3 F := hF.contMDiff.of_le (by norm_num)
  -- For small `ε` the orbits of `ε F` are the constant orbits at critical points, and these are
  -- nondegenerate with linearized flow of index `ind - n`.
  obtain ⟨ε₀, hε₀, hper⟩ :=
    h.exists_pos_forall_periodicSolutions_hamiltonianVectorField_smul_eq_image_criticalPoints
      (hF3.of_le (by norm_num))
  obtain ⟨ε₁, hε₁, hind⟩ := h.exists_pos_forall_conleyZehnderIndex_eq_manifoldMorseIndex_sub hF
  refine ⟨min ε₀ ε₁, lt_min hε₀ hε₁, fun ε hε hεle X hX Ham hXH hHam hHamε x ↦ ?_⟩
  -- The Hamiltonian is `ε F` and its vector field is `X_{ε F}`.
  obtain rfl : Ham = fun _ ↦ ε • F := funext hHamε
  obtain rfl : X = fun _ ↦ σ.hamiltonianVectorField (ε • F) :=
    funext fun t ↦ (h.isHamiltonianVectorField_iff_eq).1 (hXH t)
  have hxper := contractiblePeriodicSolutions_subset x.property
  -- The orbit is the constant orbit at a critical point.
  obtain ⟨q, -, hqx⟩ := (hper ε hε (hεle.trans (min_le_left _ _))) ▸ hxper
  have hx : ∀ t, x.val t = x.val 0 := fun t ↦ by rw [← hqx]
  obtain ⟨hmem, hnd, hΨind⟩ := hind ε hε (hεle.trans (min_le_right _ _)) x.val hxper
  refine ⟨hx, hmem, ?_⟩
  have hcrit := mem_criticalPoints.1 hmem
  -- The path of linearized flows at the critical point.
  obtain ⟨B, Ψ, hΨt⟩ := h.exists_path_mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul hF3
    hcrit ε
  have hΨ := h.symplecticFormAt_mfderiv_timeDependentFlowOf_hamiltonianVectorField_smul hF3 hcrit ε
  have hΨσ : ∀ (t : unitInterval) v w, h.symplecticFormAt (x.val 0) (Ψ t v) (Ψ t w) =
      h.symplecticFormAt (x.val 0) v w := fun t v w ↦ by rw [hΨt]; exact hΨ t v w
  -- The dimension `2 n` of `M` is even.
  have hev : 2 ∣ finrank ℝ E :=
    even_iff_two_dvd.1 (SymplecticForm.even_finrank (V := E) (h.symplecticFormAt (x.val 0)))
  have hgr := grading_eq_conleyZehnderIndex hX hσ hXH hHam hc ⟨x, OrbitCapClass.const ω c hx⟩ hnd
  rw [conleyZehnderIndex_const hσ hc hX hXH hHam hx Ψ hΨσ hΨt, hΨind Ψ hΨσ hΨt] at hgr
  have h2 : ((finrank ℝ E / 2 : ℕ) : ℝ) = (finrank ℝ E : ℝ) / 2 := Nat.cast_div hev (by norm_num)
  have hgr' : ((grading hX hσ hXH hHam hc ⟨x, OrbitCapClass.const ω c hx⟩ : ℤ) : ℝ) =
      (((manifoldMorseIndex I F (x.val 0) : ℤ) - (finrank ℝ E / 2 : ℕ) : ℤ) : ℝ) := by
    rw [hgr, Int.cast_sub, Int.cast_natCast, Int.cast_natCast, h2]
  exact_mod_cast hgr'

end CappedOrbit

end TauCeti.Floer
