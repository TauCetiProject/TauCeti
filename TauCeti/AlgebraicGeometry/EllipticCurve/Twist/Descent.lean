/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.AlgebraicGeometry.EllipticCurve.GaloisDescent
public import TauCeti.AlgebraicGeometry.EllipticCurve.VariableChange
import TauCeti.FieldTheory.GaloisCohomology.AdditiveHilbert90
import TauCeti.FieldTheory.GaloisCohomology.Hilbert90

/-!
# Effective descent for Weierstrass equations

Let `L/K` be a Galois extension, finite or infinite, with group `G = Gal(L/K)` acting on the
changes of variables `(u, r, s, t)` over `L` coefficientwise, `C ↦ σ C`. A **cocycle** of changes
of variables is a locally constant map `f : G → VariableChange L` with

`f (σ τ) = f σ * σ (f τ)`.

This file proves that every such cocycle is a coboundary: `f σ = C * (σ C)⁻¹` for some change of
variables `C` over `L`. In the language of nonabelian Galois cohomology, `H¹(G, VariableChange L)`
is trivial. The proof is a dévissage along the coordinates. The scaling `u` of a cocycle is a
cocycle with values in `Lˣ`, which is a coboundary by Hilbert 90: writing `u σ = σ x / x`,
twisting `f` by `(x⁻¹, 0, 0, 0)` makes `u ≡ 1`. On the changes with `u = 1` the coordinate `r` is
additive, so it is a cocycle with values in `L`, a coboundary by the additive Hilbert 90: writing
`r σ = σ x - x`, a twist by `(1, -x, 0, 0)` makes it vanish. Then `s` and finally `t` are dealt
with in the same way.

The consequence is **effective descent** for pointed twists. If `W` is a Weierstrass curve over
`K` and the cocycle `f` takes values in the automorphisms of `W` over `L`, that is
`f σ • W = W` over `L`, then writing `f σ = C * (σ C)⁻¹`, the curve `C⁻¹ • W` over `L` is fixed by
`G`, so it is the base change of a curve `V` over `K`. Thus every such cocycle is the cocycle
`σ ↦ C * (σ C)⁻¹` of a trivialisation `C • V = W` of a curve `V` over `K` that becomes isomorphic
to `W` over `L` (`WeierstrassCurve.exists_smul_baseChange_eq_and_eq_mul_map_inv`). This is the
half of the classification of pointed twists by `H¹(G, Aut W)` that constructs a twist from a
cohomology class.

## Main results

* `WeierstrassCurve.VariableChange.exists_eq_mul_map_inv`: a locally constant cocycle of changes
  of variables is a coboundary.
* `WeierstrassCurve.exists_smul_baseChange_eq_and_eq_mul_map_inv`: a locally constant cocycle of
  automorphisms of `W` over `L` is the cocycle of a curve over `K` isomorphic to `W` over `L`.

## References

* [J. Silverman, *The Arithmetic of Elliptic Curves*][silverman2009], X.2.2 and X.5.
* J.-P. Serre, *Galois Cohomology*, Springer, 1997, III.1.
-/

public section

namespace WeierstrassCurve

variable {K L : Type*} [Field K] [Field L] [Algebra K L]

namespace VariableChange

variable {f : Gal(L/K) → VariableChange L}

/-- Twisting a cocycle `f` by `A`, that is `σ ↦ A⁻¹ * f σ * σ A`, gives a cocycle. -/
private theorem twist_cocycle (hf : ∀ σ τ, f (σ * τ) = f σ * (f τ).map (σ : L →+* L))
    (A : VariableChange L) (σ τ : Gal(L/K)) :
    A⁻¹ * f (σ * τ) * A.map ((σ * τ : Gal(L/K)) : L →+* L) =
      A⁻¹ * f σ * A.map (σ : L →+* L) *
        (A⁻¹ * f τ * A.map (τ : L →+* L)).map (σ : L →+* L) := by
  rw [hf, map_mul, map_mul, map_inv, map_map_algEquiv]
  group

/-- Twisting a locally constant map by a change of variables keeps it locally constant. -/
private theorem isLocallyConstant_twist [Algebra.IsAlgebraic K L] (hc : IsLocallyConstant f)
    (A : VariableChange L) :
    IsLocallyConstant fun σ : Gal(L/K) ↦ A⁻¹ * f σ * A.map (σ : L →+* L) :=
  hc.comp₂ A.isLocallyConstant_map_of_isAlgebraic fun X Y ↦ A⁻¹ * X * Y

/-- If the twist of `f` by `A` is the coboundary of `C`, then `f` is the coboundary of `A * C`. -/
private theorem exists_eq_mul_map_inv_of_twist (A : VariableChange L)
    (h : ∃ C : VariableChange L, ∀ σ : Gal(L/K),
      A⁻¹ * f σ * A.map (σ : L →+* L) = C * (C.map (σ : L →+* L))⁻¹) :
    ∃ C : VariableChange L, ∀ σ : Gal(L/K), f σ = C * (C.map (σ : L →+* L))⁻¹ := by
  obtain ⟨C, hC⟩ := h
  refine ⟨A * C, fun σ ↦ ?_⟩
  calc f σ = A * (A⁻¹ * f σ * A.map (σ : L →+* L)) * (A.map (σ : L →+* L))⁻¹ := by group
    _ = A * C * ((A * C).map (σ : L →+* L))⁻¹ := by rw [hC σ, map_mul]; group

variable [IsGalois K L]

/-- The last step of the dévissage: a cocycle with `u = 1`, `r = 0` and `s = 0` is a coboundary,
its coordinate `t` being an additive cocycle. -/
private theorem exists_eq_mul_map_inv_of_u_r_s
    (hc : IsLocallyConstant f) (hf : ∀ σ τ, f (σ * τ) = f σ * (f τ).map (σ : L →+* L))
    (hu : ∀ σ, (f σ).u = 1) (hr : ∀ σ, (f σ).r = 0) (hs : ∀ σ, (f σ).s = 0) :
    ∃ C : VariableChange L, ∀ σ : Gal(L/K), f σ = C * (C.map (σ : L →+* L))⁻¹ := by
  obtain ⟨x, hx⟩ := TauCeti.isCoboundary₁_of_isCocycle₁_of_isLocallyConstant
    (f := fun σ ↦ (f σ).t) (fun σ τ ↦ by simp [hf σ τ, mul_def, hu, hr, add_comm]) (hc.comp _)
  refine ⟨⟨1, 0, 0, -x⟩, fun σ ↦ VariableChange.ext (Units.ext ?_) ?_ ?_ ?_⟩
  · simp [hu]
  · simp [hr]
  · simp [hs]
  · simp [← hx σ, AlgEquiv.smul_def, neg_add_eq_sub]

/-- The third step of the dévissage: a cocycle with `u = 1` and `r = 0` is a coboundary. Its
coordinate `s` is an additive cocycle, and twisting by its coboundary makes `s` vanish. -/
private theorem exists_eq_mul_map_inv_of_u_r
    (hc : IsLocallyConstant f) (hf : ∀ σ τ, f (σ * τ) = f σ * (f τ).map (σ : L →+* L))
    (hu : ∀ σ, (f σ).u = 1) (hr : ∀ σ, (f σ).r = 0) :
    ∃ C : VariableChange L, ∀ σ : Gal(L/K), f σ = C * (C.map (σ : L →+* L))⁻¹ := by
  obtain ⟨x, hx⟩ := TauCeti.isCoboundary₁_of_isCocycle₁_of_isLocallyConstant
    (f := fun σ ↦ (f σ).s) (fun σ τ ↦ by simp [hf σ τ, mul_def, hu, add_comm]) (hc.comp _)
  refine exists_eq_mul_map_inv_of_twist ⟨1, 0, -x, 0⟩
    (exists_eq_mul_map_inv_of_u_r_s (isLocallyConstant_twist hc _) (twist_cocycle hf _)
      (fun σ ↦ ?_) (fun σ ↦ ?_) (fun σ ↦ ?_))
  · simp [mul_def, inv_def, hu]
  · simp [mul_def, inv_def, hu, hr]
  · simp only [mul_def, inv_def, hu, hr, map_u, map_r, map_s, map_t]
    simp [← hx σ, AlgEquiv.smul_def]

/-- The second step of the dévissage: a cocycle with `u = 1` is a coboundary. Its coordinate `r`
is an additive cocycle, and twisting by its coboundary makes `r` vanish. -/
private theorem exists_eq_mul_map_inv_of_u
    (hc : IsLocallyConstant f) (hf : ∀ σ τ, f (σ * τ) = f σ * (f τ).map (σ : L →+* L))
    (hu : ∀ σ, (f σ).u = 1) :
    ∃ C : VariableChange L, ∀ σ : Gal(L/K), f σ = C * (C.map (σ : L →+* L))⁻¹ := by
  obtain ⟨x, hx⟩ := TauCeti.isCoboundary₁_of_isCocycle₁_of_isLocallyConstant
    (f := fun σ ↦ (f σ).r) (fun σ τ ↦ by simp [hf σ τ, mul_def, hu, add_comm]) (hc.comp _)
  refine exists_eq_mul_map_inv_of_twist ⟨1, -x, 0, 0⟩
    (exists_eq_mul_map_inv_of_u_r (isLocallyConstant_twist hc _) (twist_cocycle hf _)
      (fun σ ↦ ?_) (fun σ ↦ ?_))
  · simp [mul_def, inv_def, hu]
  · simp only [mul_def, inv_def, hu, map_u, map_r, map_s, map_t]
    simp [← hx σ, AlgEquiv.smul_def]

/-- **Hilbert 90 for changes of variables.** For a Galois extension `L/K`, finite or infinite,
every locally constant cocycle `f : Gal(L/K) → VariableChange L`, that is
`f (σ τ) = f σ * σ (f τ)` with `σ` acting coefficientwise, is a coboundary:
`f σ = C * (σ C)⁻¹` for some change of variables `C` over `L`. Equivalently, the first nonabelian
Galois cohomology of the changes of variables over `L` is trivial. -/
theorem exists_eq_mul_map_inv
    (hc : IsLocallyConstant f) (hf : ∀ σ τ, f (σ * τ) = f σ * (f τ).map (σ : L →+* L)) :
    ∃ C : VariableChange L, ∀ σ : Gal(L/K), f σ = C * (C.map (σ : L →+* L))⁻¹ := by
  -- The scaling `u` of `f` is a multiplicative cocycle, hence a coboundary by Hilbert 90.
  obtain ⟨x, hx⟩ := TauCeti.isMulCoboundary₁_of_isMulCocycle₁_of_isLocallyConstant
    (f := fun σ ↦ (f σ).u) (fun σ τ ↦ by
      rw [Units.ext_iff]
      simp [hf σ τ, mul_def, AlgEquiv.smul_units_def, mul_comm]) (hc.comp _)
  -- Twisting by `(x⁻¹, 0, 0, 0)` makes the scaling identically `1`.
  refine exists_eq_mul_map_inv_of_twist ⟨x⁻¹, 0, 0, 0⟩
    (exists_eq_mul_map_inv_of_u (isLocallyConstant_twist hc _) (twist_cocycle hf _)
      fun σ ↦ ?_)
  rw [Units.ext_iff]
  simp [mul_def, inv_def, ← hx σ, AlgEquiv.smul_units_def]

end VariableChange

variable [IsGalois K L]

/-- **Effective descent for pointed twists.** Let `W` be a Weierstrass curve over `K` and `L/K`
a Galois extension. Every locally constant cocycle `f : Gal(L/K) → VariableChange L` of
automorphisms of `W` over `L`, that is `f σ • W = W` over `L`, is the cocycle of a twist: there
are a Weierstrass curve `V` over `K` and a change of variables `C` over `L` with `C • V = W` over
`L` and `f σ = C * (σ C)⁻¹` for every `σ`. -/
theorem exists_smul_baseChange_eq_and_eq_mul_map_inv (W : WeierstrassCurve K)
    {f : Gal(L/K) → VariableChange L} (hc : IsLocallyConstant f)
    (hf : ∀ σ τ, f (σ * τ) = f σ * (f τ).map (σ : L →+* L))
    (hW : ∀ σ, f σ • W.baseChange L = W.baseChange L) :
    ∃ (V : WeierstrassCurve K) (C : VariableChange L), C • V.baseChange L = W.baseChange L ∧
      ∀ σ : Gal(L/K), f σ = C * (C.map (σ : L →+* L))⁻¹ := by
  obtain ⟨C, hC⟩ := VariableChange.exists_eq_mul_map_inv hc hf
  -- The curve `C⁻¹ • W` over `L` is fixed by every `σ`, since `σ C = (f σ)⁻¹ * C` fixes `W`.
  have hfix (σ : Gal(L/K)) :
      (C⁻¹ • W.baseChange L).map (σ : L →+* L) = C⁻¹ • W.baseChange L := by
    have hσ : C.map (σ : L →+* L) = (f σ)⁻¹ * C := by rw [hC σ]; group
    have hWσ : (W.baseChange L).map (σ : L →+* L) = W.baseChange L :=
      map_baseChange W (σ : L →ₐ[K] L)
    rw [← map_variableChange, VariableChange.map_inv, hσ, hWσ, mul_inv_rev, inv_inv, mul_smul,
      hW]
  obtain ⟨V, hV : V.baseChange L = C⁻¹ • W.baseChange L⟩ :=
    (mem_range_baseChange_iff_fixed _).2 hfix
  refine ⟨V, C, ?_, hC⟩
  rw [hV, smul_inv_smul]

end WeierstrassCurve
