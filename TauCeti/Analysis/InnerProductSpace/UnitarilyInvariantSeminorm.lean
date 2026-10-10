/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Analysis.Normed.Module.Seminorm.Basic
public import TauCeti.Analysis.InnerProductSpace.SingularValues

/-!
# Unitarily invariant seminorms on rectangular linear maps

A seminorm `N` on the linear maps `E →ₗ[𝕜] F` between two inner product spaces is *unitarily
invariant* when `N (U A V) = N A` for all unitaries `U` of `F` and `V` of `E`, acting
independently on the target and the source. Square operators are the case `E = F`. Unitaries are
represented as linear isometric equivalences `F ≃ₗᵢ[𝕜] F` and `E ≃ₗᵢ[𝕜] E`. The operator norm,
the Frobenius norm, the Ky Fan norms and the nuclear norm are the standard examples. By a theorem
of von Neumann, such a seminorm depends only on the singular values of its argument, which is what
lets a single Ky Fan estimate yield bounds in all of these norms at once.

This file sets up the structure together with the elementary vocabulary for comparing its
values:

* the two-sided unitary orbit `U C V` of a map `C`, on which every unitarily invariant seminorm
  and the singular values are constant;
* finite orbit certificates, which write `X` as a combination `∑ᵢ aᵢ • Uᵢ C Vᵢ` of points of the
  orbit of `C`, and bound `N X` by the coefficient mass `∑ᵢ ‖aᵢ‖` times `N C`;
* transport of a unitarily invariant seminorm along isometric isomorphisms of the source and the
  target, and to the adjoint maps;
* the zero extension of `A : E →ₗ[𝕜] F` to an endomorphism of the `L²` product `E × F`, which has
  the same singular values as `A`.

## Main declarations

* `TauCeti.UnitarilyInvariantSeminorm`: seminorms on `E →ₗ[𝕜] F` invariant under unitaries of
  the source and of the target.
* `LinearMap.twoSidedUnitaryOrbit`: the set of maps `U C V` with `U`, `V` unitary.
* `TauCeti.UnitaryOrbitCertificate`: a representation `X = ∑ᵢ aᵢ • Uᵢ C Vᵢ`, with its
  coefficient mass `TauCeti.UnitaryOrbitCertificate.mass`.
* `TauCeti.UnitaryOrbitCertificate.apply_le_mass_mul`: `N X ≤ mass * N C`.
* `TauCeti.UnitarilyInvariantSeminorm.arrowCongr`: transport along isometric isomorphisms of the
  source and the target.
* `TauCeti.UnitarilyInvariantSeminorm.compAdjoint`: the seminorm `B ↦ N B†` on the adjoint maps.
* `LinearMap.zeroExtension`, `LinearMap.singularValues_zeroExtension`: the zero extension
  `(x, y) ↦ (0, A x)` and its singular values.

## Source

The structure `UnitarilyInvariantSeminorm`, the two-sided unitary orbit, the finite orbit
certificates and the zero extension are adapted from the
[AIQ-Kitware DKPS formalization](https://github.com/AIQ-Kitware/aiq-dkps-formalization)
(`ForTauCeti/Analysis/InnerProductSpace/UnitarilyInvariantSeminorm/Basic.lean` and
`ForTauCeti/Analysis/InnerProductSpace/ZeroExtension.lean`).
Original copyright (c) 2026 Kitware, Inc.; Apache-2.0.

## References

* R. Bhatia, *Matrix Analysis*, Graduate Texts in Mathematics 169, Springer, 1997, Section IV.2.
* L. Mirsky, *Symmetric gauge functions and unitarily invariant norms*, Quart. J. Math. Oxford
  Ser. (2) **11** (1960), 50–59.
-/

public section

open Module

variable {𝕜 E F E' F' : Type*} [RCLike 𝕜]
  [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F] [InnerProductSpace 𝕜 F]
  [NormedAddCommGroup E'] [InnerProductSpace 𝕜 E'] [NormedAddCommGroup F']
  [InnerProductSpace 𝕜 F']

namespace LinearMap

/-- The **two-sided unitary orbit** of `C : E →ₗ[𝕜] F`: the maps `U ∘ C ∘ V` for unitaries `U`
of the target and `V` of the source. -/
def twoSidedUnitaryOrbit (C : E →ₗ[𝕜] F) : Set (E →ₗ[𝕜] F) :=
  {X | ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E), (U : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (V : E →ₗ[𝕜] E) = X}

theorem mem_twoSidedUnitaryOrbit {C X : E →ₗ[𝕜] F} :
    X ∈ C.twoSidedUnitaryOrbit ↔
      ∃ (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E), (U : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (V : E →ₗ[𝕜] E) = X :=
  Iff.rfl

theorem linearIsometryEquiv_comp_comp_mem_twoSidedUnitaryOrbit (C : E →ₗ[𝕜] F)
    (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) :
    (U : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (V : E →ₗ[𝕜] E) ∈ C.twoSidedUnitaryOrbit :=
  ⟨U, V, rfl⟩

@[simp]
theorem self_mem_twoSidedUnitaryOrbit (C : E →ₗ[𝕜] F) : C ∈ C.twoSidedUnitaryOrbit :=
  ⟨.refl 𝕜 F, .refl 𝕜 E, rfl⟩

/-- Two-sided unitary orbits are equivalence classes: the orbit of any of its points is the whole
orbit. -/
theorem twoSidedUnitaryOrbit_eq_of_mem {C X : E →ₗ[𝕜] F} (h : X ∈ C.twoSidedUnitaryOrbit) :
    X.twoSidedUnitaryOrbit = C.twoSidedUnitaryOrbit := by
  obtain ⟨U, V, rfl⟩ := h
  ext Y
  constructor
  · rintro ⟨U', V', rfl⟩
    exact ⟨U.trans U', V'.trans V, by ext; simp⟩
  · rintro ⟨U', V', rfl⟩
    exact ⟨U.symm.trans U', V'.trans V.symm, by ext; simp⟩

/-- Maps in the same two-sided unitary orbit have the same singular values. -/
theorem singularValues_eq_of_mem_twoSidedUnitaryOrbit [FiniteDimensional 𝕜 E]
    [FiniteDimensional 𝕜 F] {C X : E →ₗ[𝕜] F} (h : X ∈ C.twoSidedUnitaryOrbit) :
    X.singularValues = C.singularValues := by
  obtain ⟨U, V, rfl⟩ := h
  simp

end LinearMap

namespace TauCeti

/-- A **unitarily invariant seminorm** on the linear maps `E →ₗ[𝕜] F`: a seminorm `N` with
`N (U ∘ A ∘ V) = N A` for every unitary `U` of the target `F` and every unitary `V` of the source
`E`, acting independently. Square operators are the case `E = F`. -/
structure UnitarilyInvariantSeminorm (𝕜 E F : Type*) [RCLike 𝕜]
    [NormedAddCommGroup E] [InnerProductSpace 𝕜 E] [NormedAddCommGroup F]
    [InnerProductSpace 𝕜 F] extends Seminorm 𝕜 (E →ₗ[𝕜] F) where
  /-- Invariance under unitaries of the target and of the source. -/
  map_linearIsometryEquiv_comp_comp' (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] F) :
    toSeminorm ((U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)) = toSeminorm A

namespace UnitarilyInvariantSeminorm

instance : FunLike (UnitarilyInvariantSeminorm 𝕜 E F) (E →ₗ[𝕜] F) ℝ where
  coe N := N.toFun
  coe_injective := by
    rintro ⟨N, _⟩ ⟨M, _⟩ h
    congr
    exact Seminorm.ext (congrFun h)

instance : SeminormClass (UnitarilyInvariantSeminorm 𝕜 E F) 𝕜 (E →ₗ[𝕜] F) where
  map_zero N := N.map_zero'
  map_add_le_add N := N.add_le'
  map_neg_eq_map N := N.neg'
  map_smul_eq_mul N := N.smul'

@[ext]
theorem ext {N M : UnitarilyInvariantSeminorm 𝕜 E F} (h : ∀ A, N A = M A) : N = M :=
  DFunLike.ext N M h

@[simp]
theorem coe_toSeminorm (N : UnitarilyInvariantSeminorm 𝕜 E F) : ⇑N.toSeminorm = N :=
  (rfl)

variable (N : UnitarilyInvariantSeminorm 𝕜 E F)

/-- **Unitary invariance**: `N (U ∘ A ∘ V) = N A` for unitaries `U` of the target and `V` of the
source. -/
theorem map_linearIsometryEquiv_comp_comp (U : F ≃ₗᵢ[𝕜] F) (V : E ≃ₗᵢ[𝕜] E)
    (A : E →ₗ[𝕜] F) : N ((U : F →ₗ[𝕜] F) ∘ₗ A ∘ₗ (V : E →ₗ[𝕜] E)) = N A :=
  N.map_linearIsometryEquiv_comp_comp' U V A

@[simp]
theorem map_linearIsometryEquiv_comp (U : F ≃ₗᵢ[𝕜] F) (A : E →ₗ[𝕜] F) :
    N ((U : F →ₗ[𝕜] F) ∘ₗ A) = N A := by
  convert N.map_linearIsometryEquiv_comp_comp U (.refl 𝕜 E) A using 2
  ext; simp

@[simp]
theorem map_comp_linearIsometryEquiv (V : E ≃ₗᵢ[𝕜] E) (A : E →ₗ[𝕜] F) :
    N (A ∘ₗ (V : E →ₗ[𝕜] E)) = N A := by
  convert N.map_linearIsometryEquiv_comp_comp (.refl 𝕜 F) V A using 2
  ext; simp

/-- A unitarily invariant seminorm is constant on each two-sided unitary orbit. -/
theorem map_eq_of_mem_twoSidedUnitaryOrbit {C X : E →ₗ[𝕜] F}
    (h : X ∈ C.twoSidedUnitaryOrbit) : N X = N C := by
  obtain ⟨U, V, rfl⟩ := h
  exact N.map_linearIsometryEquiv_comp_comp U V C

/-! ### Transport along isometric isomorphisms -/

/-- The value of `N` on maps `E' →ₗ[𝕜] F'` read through isometric isomorphisms `E ≃ E'` and
`F ≃ F'`; `UnitarilyInvariantSeminorm.arrowCongr` packages it as an equivalence. -/
private noncomputable def transport (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F')
    (N : UnitarilyInvariantSeminorm 𝕜 E F) : UnitarilyInvariantSeminorm 𝕜 E' F' where
  toSeminorm := N.toSeminorm.comp
    (LinearEquiv.arrowCongr eE.toLinearEquiv eF.toLinearEquiv).symm.toLinearMap
  map_linearIsometryEquiv_comp_comp' U V A := by
    -- Conjugating `U` and `V` back to `F` and `E` turns `U ∘ A ∘ V` into a two-sided unitary
    -- multiple of the transported map.
    have h := N.map_linearIsometryEquiv_comp_comp (eF.trans (U.trans eF.symm))
      (eE.trans (V.trans eE.symm)) ((eF.symm : F' →ₗ[𝕜] F) ∘ₗ A ∘ₗ (eE : E →ₗ[𝕜] E'))
    rw [Seminorm.comp_apply, Seminorm.comp_apply, coe_toSeminorm]
    convert h using 2 <;> ext <;> simp

private theorem transport_apply (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F')
    (N : UnitarilyInvariantSeminorm 𝕜 E F) (A : E' →ₗ[𝕜] F') :
    transport eE eF N A = N ((eF.symm : F' →ₗ[𝕜] F) ∘ₗ A ∘ₗ (eE : E →ₗ[𝕜] E')) :=
  (rfl)

/-- **Transport** of unitarily invariant seminorms along isometric isomorphisms `eE : E ≃ E'` of
the sources and `eF : F ≃ F'` of the targets: `N` corresponds to the seminorm
`A ↦ N (eF⁻¹ ∘ A ∘ eE)` on `E' →ₗ[𝕜] F'`, which is again unitarily invariant. -/
noncomputable def arrowCongr (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F') :
    UnitarilyInvariantSeminorm 𝕜 E F ≃ UnitarilyInvariantSeminorm 𝕜 E' F' where
  toFun := transport eE eF
  invFun := transport eE.symm eF.symm
  left_inv N := by ext; rw [transport_apply, transport_apply]; congr 1; ext; simp
  right_inv N := by ext; rw [transport_apply, transport_apply]; congr 1; ext; simp

@[simp]
theorem arrowCongr_apply (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F') (A : E' →ₗ[𝕜] F') :
    arrowCongr eE eF N A = N ((eF.symm : F' →ₗ[𝕜] F) ∘ₗ A ∘ₗ (eE : E →ₗ[𝕜] E')) :=
  transport_apply eE eF N A

@[simp]
theorem arrowCongr_symm (eE : E ≃ₗᵢ[𝕜] E') (eF : F ≃ₗᵢ[𝕜] F') :
    (arrowCongr (𝕜 := 𝕜) eE eF).symm = arrowCongr eE.symm eF.symm :=
  (rfl)

/-- Transport along unitaries of the source and the target leaves every unitarily invariant
seminorm unchanged. -/
@[simp]
theorem arrowCongr_eq_self (U : E ≃ₗᵢ[𝕜] E) (V : F ≃ₗᵢ[𝕜] F) : arrowCongr U V N = N := by
  ext A
  rw [arrowCongr_apply, map_linearIsometryEquiv_comp_comp]

/-! ### Transport to the adjoint maps -/

section Adjoint

variable [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]

/-- The **adjoint transport** of a unitarily invariant seminorm `N` on `E →ₗ[𝕜] F`: the seminorm
`B ↦ N B†` on `F →ₗ[𝕜] E`, again unitarily invariant. -/
noncomputable def compAdjoint : UnitarilyInvariantSeminorm 𝕜 F E where
  toSeminorm := N.toSeminorm.comp (LinearMap.adjoint (𝕜 := 𝕜) (E := F) (F := E)).toLinearMap
  map_linearIsometryEquiv_comp_comp' U V B := by
    rw [Seminorm.comp_apply, Seminorm.comp_apply]
    simpa [LinearMap.adjoint_comp, LinearMap.comp_assoc] using
      N.map_linearIsometryEquiv_comp_comp V.symm U.symm (LinearMap.adjoint B)

@[simp]
theorem compAdjoint_apply (B : F →ₗ[𝕜] E) : N.compAdjoint B = N (LinearMap.adjoint B) :=
  (rfl)

@[simp]
theorem compAdjoint_compAdjoint : N.compAdjoint.compAdjoint = N := by
  ext A
  simp

end Adjoint

end UnitarilyInvariantSeminorm

/-! ### Finite orbit certificates -/

/-- A **finite unitary orbit certificate** for `X` over `C`, indexed by a finite type `ι`: a
representation `X = ∑ᵢ aᵢ • Uᵢ ∘ C ∘ Vᵢ` of `X` as a linear combination of points of the
two-sided unitary orbit of `C`. Its coefficient mass `∑ᵢ ‖aᵢ‖` bounds every unitarily invariant
seminorm of `X` by the same seminorm of `C`
(`TauCeti.UnitaryOrbitCertificate.apply_le_mass_mul`). -/
@[ext]
structure UnitaryOrbitCertificate (ι : Type*) [Fintype ι] (C X : E →ₗ[𝕜] F) where
  /-- The coefficients `aᵢ`. -/
  coeff : ι → 𝕜
  /-- The unitaries `Uᵢ` of the target. -/
  left : ι → F ≃ₗᵢ[𝕜] F
  /-- The unitaries `Vᵢ` of the source. -/
  right : ι → E ≃ₗᵢ[𝕜] E
  /-- The representation `∑ᵢ aᵢ • Uᵢ ∘ C ∘ Vᵢ = X`. -/
  sum_smul_comp_comp_eq :
    ∑ i, coeff i • ((left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (right i : E →ₗ[𝕜] E)) = X

namespace UnitaryOrbitCertificate

variable {ι κ : Type*} [Fintype ι] [Fintype κ] {C X : E →ₗ[𝕜] F}
  (c : UnitaryOrbitCertificate ι C X)

/-- The **coefficient mass** `∑ᵢ ‖aᵢ‖` of an orbit certificate. -/
noncomputable def mass : ℝ :=
  ∑ i, ‖c.coeff i‖

theorem mass_def : c.mass = ∑ i, ‖c.coeff i‖ :=
  (rfl)

theorem mass_nonneg : 0 ≤ c.mass :=
  Finset.sum_nonneg fun _ _ ↦ norm_nonneg _

/-- **Certificate bound**: if `X` has an orbit certificate over `C` of mass `m`, then
`N X ≤ m * N C` for every unitarily invariant seminorm `N`. -/
theorem apply_le_mass_mul (N : UnitarilyInvariantSeminorm 𝕜 E F) : N X ≤ c.mass * N C := by
  calc N X = N (∑ i, c.coeff i • ((c.left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (c.right i : E →ₗ[𝕜] E))) := by
        rw [c.sum_smul_comp_comp_eq]
    _ ≤ ∑ i, N (c.coeff i • ((c.left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (c.right i : E →ₗ[𝕜] E))) :=
        Finset.le_sum_of_subadditive N (map_zero N).le (map_add_le_add N) _ _
    _ = c.mass * N C := by
        simp [mass_def, Finset.sum_mul, map_smul_eq_mul, N.map_linearIsometryEquiv_comp_comp]

/-- **Reindexing** an orbit certificate along an equivalence of its finite index types. -/
def reindex (e : ι ≃ κ) : UnitaryOrbitCertificate κ C X where
  coeff := c.coeff ∘ e.symm
  left := c.left ∘ e.symm
  right := c.right ∘ e.symm
  sum_smul_comp_comp_eq := (e.symm.sum_comp fun i ↦
    c.coeff i • ((c.left i : F →ₗ[𝕜] F) ∘ₗ C ∘ₗ (c.right i : E →ₗ[𝕜] E))).trans
      c.sum_smul_comp_comp_eq

@[simp]
theorem coeff_reindex (e : ι ≃ κ) (k : κ) : (c.reindex e).coeff k = c.coeff (e.symm k) :=
  (rfl)

@[simp]
theorem left_reindex (e : ι ≃ κ) (k : κ) : (c.reindex e).left k = c.left (e.symm k) :=
  (rfl)

@[simp]
theorem right_reindex (e : ι ≃ κ) (k : κ) : (c.reindex e).right k = c.right (e.symm k) :=
  (rfl)

@[simp]
theorem mass_reindex (e : ι ≃ κ) : (c.reindex e).mass = c.mass := by
  simp only [mass_def, coeff_reindex]
  exact e.symm.sum_comp fun i ↦ ‖c.coeff i‖

end UnitaryOrbitCertificate

end TauCeti

/-! ### Zero extension to the square `L²` product -/

namespace LinearMap

/-- The **zero extension** of `A : E →ₗ[𝕜] F` to an endomorphism of the `L²` product `E × F`:
the map `(x, y) ↦ (0, A x)`. -/
noncomputable def zeroExtension (A : E →ₗ[𝕜] F) : WithLp 2 (E × F) →ₗ[𝕜] WithLp 2 (E × F) :=
  (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ inr 𝕜 E F ∘ₗ A ∘ₗ WithLp.fstₗ 2 𝕜 E F

@[simp]
theorem zeroExtension_apply (A : E →ₗ[𝕜] F) (z : WithLp 2 (E × F)) :
    A.zeroExtension z = WithLp.toLp 2 (0, A z.fst) :=
  (rfl)

/-- **Singular values of the zero extension**: extending `A : E →ₗ[𝕜] F` by zero to an
endomorphism of the `L²` product `E × F` leaves its zero-padded singular-value sequence
unchanged. -/
@[simp]
theorem singularValues_zeroExtension [FiniteDimensional 𝕜 E] [FiniteDimensional 𝕜 F]
    (A : E →ₗ[𝕜] F) : A.zeroExtension.singularValues = A.singularValues := by
  -- `A.zeroExtension = B ∘ fst` for `B = (0, A ·)`, and the adjoint of `fst` is the inclusion
  -- of the first factor; both `B` and that inclusion preserve norms.
  set B : E →ₗ[𝕜] WithLp 2 (E × F) :=
    (WithLp.linearEquiv 2 𝕜 (E × F)).symm.toLinearMap ∘ₗ inr 𝕜 E F ∘ₗ A
  have hB : B.singularValues = A.singularValues :=
    singularValues_eq_of_norm_apply_eq fun x ↦ by simp [B, WithLp.norm_toLp_snd]
  have hA : A.zeroExtension = B ∘ₗ WithLp.fstₗ 2 𝕜 E F := rfl
  rw [hA, ← singularValues_adjoint, adjoint_comp, WithLp.adjoint_fstₗ, ← hB,
    ← singularValues_adjoint B]
  exact singularValues_eq_of_norm_apply_eq fun x ↦ by simp [WithLp.norm_toLp_fst]

end LinearMap
