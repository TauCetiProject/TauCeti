/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.LinearAlgebra.FiniteBilinearModule.Primary.Decomposition
public import TauCeti.LinearAlgebra.IntegralLattice.Discriminant.Quadratic
public import TauCeti.NumberTheory.IntegralLattice.Genus
public import TauCeti.NumberTheory.IntegralLattice.Localization.Discriminant.Basic
import TauCeti.LinearAlgebra.BilinearForm.Isometry.Basic
import TauCeti.NumberTheory.IntegralLattice.Localization.Ideals
import TauCeti.NumberTheory.Padics.RatCast

/-!
# Discriminant forms are local, and invariants of the genus

Let `L` be a nondegenerate integral lattice with discriminant group `A_L = Lᵛ / L` and discriminant
pairing `b_L(x, y) = B(x, y) mod ℤ`, and let `p` be a prime. The `p`-primary component of `A_L` is
the discriminant group `(ℤ_p ⊗[ℤ] Lᵛ) / L_p` of the localization `L_p = ℤ_p ⊗[ℤ] L`
(`TauCeti.IntegralLattice.primaryComponentEquivLocalDiscriminantGroup`). This file shows that the
pairing on it is determined by `L_p` too: an isometry `φ : L_p ≃ M_p` of localizations induces an
isometry between the `p`-primary components of `b_L` and `b_M`, and, for even lattices, between
the `p`-primary components of the discriminant quadratic forms `q_L(x) = B(x, x) / 2 mod ℤ`.

The isometry `φ` extends to the completed rational spaces and carries the dual of `L_p` onto the
dual of `M_p`, hence induces an equivalence of the local discriminant groups. On representatives
`x, y ∈ Lᵛ` of `p`-primary classes, with representatives `x', y' ∈ Mᵛ` of the transported classes,
the values `B(x', y')` and `B(x, y)` differ by an element of `ℤ_p`, since `x'` and `φ x` differ by a
vector of `M_p`. Both values have `p`-power denominators, because their classes are killed by a
power of `p`, and a rational number with `p`-power denominator that lies in `ℤ_p` is an integer
(`Padic.den_eq_one_of_pow_mul_eq_of_norm_rat_le_one`). So `b_M(x', y') = b_L(x, y)`; the same
argument applies to the half-norms when the lattices are even.

Lattices in one genus have isometric localizations at every prime and the same order of
discriminant group, so their discriminant forms are isometric prime by prime, and hence isometric
(`TauCeti.FiniteBilinearModule.nonempty_isometry_of_forall_primaryComponent`). This is the easy
half of Nikulin's description of the genus of an even lattice by its signature and its
discriminant quadratic form, Corollary 1.9.4, and of its odd analogue, Corollary 1.16.3, where the
discriminant bilinear form replaces the quadratic one.

## Main declarations

* `TauCeti.IntegralLattice.primaryDiscriminantBilinearIsometry`: an isometry `L_p ≃ M_p` induces
  an isometry of the `p`-primary components of the discriminant bilinear modules.
* `TauCeti.IntegralLattice.primaryDiscriminantQuadraticIsometry`: for even lattices, it induces an
  isometry of the `p`-primary components of the discriminant quadratic modules.
* `TauCeti.IntegralLattice.SameGenus.nonempty_isometry_discriminantBilinearModule`: lattices in one
  genus have isometric discriminant bilinear modules.
* `TauCeti.IntegralLattice.SameGenus.nonempty_isometry_discriminantQuadraticModule`: even lattices
  in one genus have isometric discriminant quadratic modules.

## References

* V. V. Nikulin, *Integral symmetric bilinear forms and some of their applications*, §1.9 and
  §1.16.
* J. H. Conway and N. J. A. Sloane, *Sphere Packings, Lattices and Groups*, Chapter 15, §7.
-/

public section

open Module TensorProduct AddCommGroup

namespace TauCeti.IntegralLattice

variable {V W : Type*} [AddCommGroup V] [Module ℚ V] [AddCommGroup W] [Module ℚ W]
variable {p : ℕ} [Fact p.Prime] {L : IntegralLattice V} {M : IntegralLattice W}

/-! ### Representatives of `p`-primary classes -/

omit [Fact p.Prime] in
/-- A representative of a `p`-primary discriminant class has a `p`-power multiple in `L`. -/
private theorem exists_pow_smul_mem_carrierInDual {x : L.dualCarrier}
    (hx : (Submodule.Quotient.mk x : L.DiscriminantGroup) ∈
      primaryComponent L.DiscriminantGroup p) :
    ∃ k : ℕ, p ^ k • x ∈ L.carrierInDual := by
  obtain ⟨k, hk⟩ := mem_primaryComponent.mp hx
  exact ⟨k, (Submodule.Quotient.mk_eq_zero _).mp (by rw [Submodule.Quotient.mk_smul]; exact hk)⟩

omit [Fact p.Prime] in
/-- The form pairs a representative of a `p`-primary discriminant class with any dual vector into
`p`-power denominators. -/
private theorem exists_pow_mul_form_eq_intCast {x : L.dualCarrier}
    (hx : (Submodule.Quotient.mk x : L.DiscriminantGroup) ∈
      primaryComponent L.DiscriminantGroup p)
    (y : L.dualCarrier) : ∃ (k : ℕ) (n : ℤ), (p : ℚ) ^ k * L.form x y = n := by
  obtain ⟨k, hk⟩ := exists_pow_smul_mem_carrierInDual hx
  have h0 :
      L.discriminantPairing (Submodule.Quotient.mk (p ^ k • x)) (Submodule.Quotient.mk y) = 0 := by
    rw [(Submodule.Quotient.mk_eq_zero _).mpr hk, map_zero, LinearMap.zero_apply]
  obtain ⟨n, hn⟩ := Submodule.mem_one.mp ((L.discriminantPairing_mk_eq_zero_iff _ _).mp h0)
  refine ⟨k, n, ?_⟩
  rw [eq_intCast] at hn
  simp only [hn, Submodule.coe_smul_of_tower, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
    Nat.cast_pow]

omit [Fact p.Prime] in
/-- For an even lattice, the half-norm of a representative of a `p`-primary discriminant class has
`p`-power denominator. -/
private theorem exists_pow_mul_form_self_div_two_eq_intCast (hL : L.IsEven) {x : L.dualCarrier}
    (hx : (Submodule.Quotient.mk x : L.DiscriminantGroup) ∈
      primaryComponent L.DiscriminantGroup p) :
    ∃ (k : ℕ) (n : ℤ), (p : ℚ) ^ k * (L.form x x / 2) = n := by
  obtain ⟨k, hk⟩ := exists_pow_smul_mem_carrierInDual hx
  have h0 : L.discriminantQuadraticMap hL (Submodule.Quotient.mk (p ^ k • x)) = 0 := by
    rw [(Submodule.Quotient.mk_eq_zero _).mpr hk, map_zero]
  obtain ⟨n, hn⟩ := (L.discriminantQuadraticMap_mk_eq_zero_iff hL _).mp h0
  refine ⟨2 * k, n, ?_⟩
  simp only [Submodule.coe_smul_of_tower, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul] at hn
  push_cast at hn ⊢
  linear_combination hn / 2

/-- The completed rational form on two dual vectors of `L`. -/
private theorem completedRationalForm_localizationDualToCompletion_one_tmul (x y : L.dualCarrier) :
    L.completedRationalForm p (L.localizationDualToCompletion p (1 ⊗ₜ x))
        (L.localizationDualToCompletion p (1 ⊗ₜ y)) = ((L.form x y : ℚ) : ℚ_[p]) := by
  simp

variable [L.IsNondegenerate] [M.IsNondegenerate]

/-! ### Transport along an isometry of localizations -/

/-- An isometry `L_p ≃ M_p` transports the localized dual carrier of `L` to that of `M`, through
the perfect pairings with the localized carriers. -/
private noncomputable def localDualCarrierEquiv
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p)) :
    L.LocalDualCarrier p ≃ₗ[ℤ_[p]] M.LocalDualCarrier p :=
  (L.localDualPairingEquiv p).trans
    (φ.toLinearEquiv.symm.dualMap.trans (M.localDualPairingEquiv p).symm)

private theorem localDualPairingEquiv_localDualCarrierEquiv
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p))
    (u : L.LocalDualCarrier p) (x : L.LocalCarrier p) :
    M.localDualPairingEquiv p (localDualCarrierEquiv φ u) (φ x) =
      L.localDualPairingEquiv p u x := by
  rw [localDualCarrierEquiv, LinearEquiv.trans_apply, LinearEquiv.trans_apply,
    LinearEquiv.apply_symm_apply, LinearEquiv.dualMap_apply]
  exact congrArg _ (φ.toLinearEquiv.symm_apply_apply x)

/-- In the completed rational spaces, the transported dual carrier is the image of the dual
carrier under the extension of `φ`. -/
private theorem completedIsometryEquiv_localizationDualToCompletion
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p))
    (u : L.LocalDualCarrier p) :
    completedIsometryEquiv p φ (L.localizationDualToCompletion p u) =
      M.localizationDualToCompletion p (localDualCarrierEquiv φ u) := by
  apply LinearMap.ker_eq_bot.mp
    ((M.nondegenerate_completedRationalForm_iff p).mpr M.form_nondegenerate).ker_eq_bot
  apply LinearMap.ext_on (M.span_range_localizationToCompletion p)
  rintro w ⟨y, rfl⟩
  obtain ⟨x, rfl⟩ := φ.surjective y
  calc M.completedRationalForm p (completedIsometryEquiv p φ (L.localizationDualToCompletion p u))
          (M.localizationToCompletion p (φ x))
      = L.completedRationalForm p (L.localizationDualToCompletion p u)
          (L.localizationToCompletion p x) := by
        rw [← completedIsometryEquiv_localizationToCompletion,
          LinearMap.BilinForm.IsometryEquiv.map_app]
    _ = M.completedRationalForm p (M.localizationDualToCompletion p (localDualCarrierEquiv φ u))
          (M.localizationToCompletion p (φ x)) := by
        rw [completedRationalForm_localizationDualToCompletion,
          completedRationalForm_localizationDualToCompletion,
          localDualPairingEquiv_localDualCarrierEquiv]

private theorem localDualCarrierEquiv_localCarrierToDual
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p)) (x : L.LocalCarrier p) :
    localDualCarrierEquiv φ (L.localCarrierToDual p x) = M.localCarrierToDual p (φ x) :=
  M.localizationDualToCompletion_injective p <| by
    rw [← completedIsometryEquiv_localizationDualToCompletion,
      localizationDualToCompletion_localCarrierToDual,
      localizationDualToCompletion_localCarrierToDual,
      completedIsometryEquiv_localizationToCompletion]

/-- An isometry `L_p ≃ M_p` induces an equivalence of the discriminant groups of `L_p` and
`M_p`. -/
private noncomputable def localDiscriminantGroupEquiv
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p)) :
    L.LocalDiscriminantGroup p ≃ₗ[ℤ_[p]] M.LocalDiscriminantGroup p :=
  Submodule.Quotient.equiv _ _ (localDualCarrierEquiv φ) <| by
    have h : (localDualCarrierEquiv φ : _ →ₗ[ℤ_[p]] _) ∘ₗ L.localCarrierToDual p =
        M.localCarrierToDual p ∘ₗ (φ.toLinearEquiv : _ →ₗ[ℤ_[p]] _) :=
      LinearMap.ext (localDualCarrierEquiv_localCarrierToDual φ)
    rw [← LinearMap.range_comp, h, LinearMap.range_comp_of_range_eq_top _ (LinearEquiv.range _)]

/-- An isometry `L_p ≃ M_p` induces an additive equivalence of the `p`-primary components of the
discriminant groups. -/
private noncomputable def primaryComponentEquiv
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p)) :
    primaryComponent L.DiscriminantGroup p ≃+ primaryComponent M.DiscriminantGroup p :=
  (L.primaryComponentEquivLocalDiscriminantGroup p).trans
    ((localDiscriminantGroupEquiv φ).toAddEquiv.trans
      (M.primaryComponentEquivLocalDiscriminantGroup p).symm)

/-- After localization, a representative of the transport of a `p`-primary class is the transport
of a representative, up to a vector of `M_p`. -/
private theorem exists_one_tmul_eq_add
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p))
    {a : primaryComponent L.DiscriminantGroup p} {x : L.dualCarrier}
    (hx : Submodule.Quotient.mk x = (a : L.DiscriminantGroup)) {x' : M.dualCarrier}
    (hx' : Submodule.Quotient.mk x' = (primaryComponentEquiv φ a : M.DiscriminantGroup)) :
    ∃ m : M.LocalCarrier p, (1 : ℤ_[p]) ⊗ₜ x' =
      localDualCarrierEquiv φ ((1 : ℤ_[p]) ⊗ₜ x) + M.localCarrierToDual p m := by
  have ha : a = ⟨_, hx ▸ a.2⟩ := Subtype.ext hx.symm
  have ha' : primaryComponentEquiv φ a = ⟨_, hx' ▸ (primaryComponentEquiv φ a).2⟩ :=
    Subtype.ext hx'.symm
  have h : M.primaryComponentEquivLocalDiscriminantGroup p (primaryComponentEquiv φ a) =
      localDiscriminantGroupEquiv φ (L.primaryComponentEquivLocalDiscriminantGroup p a) :=
    (M.primaryComponentEquivLocalDiscriminantGroup p).apply_symm_apply _
  rw [ha', primaryComponentEquivLocalDiscriminantGroup_apply_mk] at h
  conv_rhs at h => rw [ha, primaryComponentEquivLocalDiscriminantGroup_apply_mk]
  rw [localDiscriminantGroupEquiv, Submodule.Quotient.equiv_apply,
    Submodule.mapQ_apply, Submodule.Quotient.eq] at h
  obtain ⟨m, hm⟩ := h
  exact ⟨m, by rw [hm, LinearEquiv.coe_coe, add_sub_cancel]⟩

/-- The completed rational form of `M` on transported dual vectors is the form of `L`. -/
private theorem completedRationalForm_localDualCarrierEquiv_one_tmul
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p)) (x y : L.dualCarrier) :
    M.completedRationalForm p
      (M.localizationDualToCompletion p (localDualCarrierEquiv φ (1 ⊗ₜ x)))
      (M.localizationDualToCompletion p (localDualCarrierEquiv φ (1 ⊗ₜ y))) =
        ((L.form x y : ℚ) : ℚ_[p]) := by
  rw [← completedIsometryEquiv_localizationDualToCompletion,
    ← completedIsometryEquiv_localizationDualToCompletion,
    LinearMap.BilinForm.IsometryEquiv.map_app,
    completedRationalForm_localizationDualToCompletion_one_tmul]

/-- The completed rational form on transported dual vectors and vectors of `M_p` differs from the
form on the original dual vectors by an element of `ℤ_p`. -/
private theorem exists_form_eq_add_algebraMap
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p))
    {x y : L.dualCarrier} {x' y' : M.dualCarrier} {m n : M.LocalCarrier p}
    (hm : (1 : ℤ_[p]) ⊗ₜ x' = localDualCarrierEquiv φ (1 ⊗ₜ x) + M.localCarrierToDual p m)
    (hn : (1 : ℤ_[p]) ⊗ₜ y' = localDualCarrierEquiv φ (1 ⊗ₜ y) + M.localCarrierToDual p n) :
    ∃ z : ℤ_[p], ((M.form x' y' : ℚ) : ℚ_[p]) =
      ((L.form x y : ℚ) : ℚ_[p]) + algebraMap ℤ_[p] ℚ_[p] z := by
  have hψ := completedRationalForm_localDualCarrierEquiv_one_tmul φ x y
  refine ⟨M.localDualPairingEquiv p (localDualCarrierEquiv φ (1 ⊗ₜ y)) m +
    M.localDualPairingEquiv p (localDualCarrierEquiv φ (1 ⊗ₜ x)) n + M.localIntegralForm p m n, ?_⟩
  rw [← completedRationalForm_localizationDualToCompletion_one_tmul, hm, hn]
  simp only [map_add, LinearMap.add_apply, localizationDualToCompletion_localCarrierToDual, hψ,
    completedRationalForm_localizationDualToCompletion,
    completedRationalForm_localizationToCompletion]
  rw [(M.isSymm_completedRationalForm p).eq (M.localizationToCompletion p m),
    completedRationalForm_localizationDualToCompletion]
  ring

/-- For an even lattice `M`, the half-norm on a transported dual vector shifted by a vector of
`M_p` differs from the half-norm on the original dual vector by an element of `ℤ_p`. -/
private theorem exists_form_self_div_two_eq_add_algebraMap (hM : M.IsEven)
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p))
    {x : L.dualCarrier} {x' : M.dualCarrier} {m : M.LocalCarrier p}
    (hm : (1 : ℤ_[p]) ⊗ₜ x' = localDualCarrierEquiv φ (1 ⊗ₜ x) + M.localCarrierToDual p m) :
    ∃ z : ℤ_[p], ((M.form x' x' / 2 : ℚ) : ℚ_[p]) =
      ((L.form x x / 2 : ℚ) : ℚ_[p]) + algebraMap ℤ_[p] ℚ_[p] z := by
  obtain ⟨w, hw⟩ := hM.two_dvd_localIntegralForm_apply_self m
  refine ⟨M.localDualPairingEquiv p (localDualCarrierEquiv φ (1 ⊗ₜ x)) m + w, ?_⟩
  have h := completedRationalForm_localizationDualToCompletion_one_tmul (p := p) x' x'
  rw [hm] at h
  simp only [map_add, LinearMap.add_apply, localizationDualToCompletion_localCarrierToDual,
    completedRationalForm_localDualCarrierEquiv_one_tmul,
    completedRationalForm_localizationDualToCompletion,
    completedRationalForm_localizationToCompletion, hw] at h
  rw [(M.isSymm_completedRationalForm p).eq (M.localizationToCompletion p m),
    completedRationalForm_localizationDualToCompletion] at h
  rw [map_add, Rat.cast_div, Rat.cast_div, Rat.cast_ofNat]
  rw [map_mul, map_ofNat] at h
  linear_combination -h / 2

/-- The transport of `p`-primary classes along `φ` preserves the discriminant pairing. -/
private theorem discriminantPairing_primaryComponentEquiv
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p))
    (a b : primaryComponent L.DiscriminantGroup p) :
    M.discriminantPairing (primaryComponentEquiv φ a) (primaryComponentEquiv φ b) =
      L.discriminantPairing a b := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (a : L.DiscriminantGroup)
  obtain ⟨y, hy⟩ := Submodule.Quotient.mk_surjective _ (b : L.DiscriminantGroup)
  obtain ⟨x', hx'⟩ :=
    Submodule.Quotient.mk_surjective _ (primaryComponentEquiv φ a : M.DiscriminantGroup)
  obtain ⟨y', hy'⟩ :=
    Submodule.Quotient.mk_surjective _ (primaryComponentEquiv φ b : M.DiscriminantGroup)
  obtain ⟨m, hm⟩ := exists_one_tmul_eq_add φ hx hx'
  obtain ⟨n, hn⟩ := exists_one_tmul_eq_add φ hy hy'
  obtain ⟨k, c, hc⟩ := exists_pow_mul_form_eq_intCast (hx ▸ a.2) y
  obtain ⟨k', c', hc'⟩ :=
    exists_pow_mul_form_eq_intCast (hx' ▸ (primaryComponentEquiv φ a).2) y'
  obtain ⟨z, hz⟩ := exists_form_eq_add_algebraMap φ hm hn
  rw [← hx, ← hy, ← hx', ← hy', discriminantPairing_mk, discriminantPairing_mk]
  refine Padic.addCircle_coe_eq_coe_of_eq_add_algebraMap (k := k + k')
    (n := p ^ k * c' - p ^ k' * c) ?_ hz
  push_cast
  linear_combination (p : ℚ) ^ k * hc' - (p : ℚ) ^ k' * hc

/-- For even lattices, the transport of `p`-primary classes along `φ` preserves the discriminant
quadratic map. -/
private theorem discriminantQuadraticMap_primaryComponentEquiv (hL : L.IsEven) (hM : M.IsEven)
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p))
    (a : primaryComponent L.DiscriminantGroup p) :
    M.discriminantQuadraticMap hM (primaryComponentEquiv φ a) =
      L.discriminantQuadraticMap hL a := by
  obtain ⟨x, hx⟩ := Submodule.Quotient.mk_surjective _ (a : L.DiscriminantGroup)
  obtain ⟨x', hx'⟩ :=
    Submodule.Quotient.mk_surjective _ (primaryComponentEquiv φ a : M.DiscriminantGroup)
  obtain ⟨m, hm⟩ := exists_one_tmul_eq_add φ hx hx'
  obtain ⟨k, c, hc⟩ := exists_pow_mul_form_self_div_two_eq_intCast hL (hx ▸ a.2)
  obtain ⟨k', c', hc'⟩ :=
    exists_pow_mul_form_self_div_two_eq_intCast hM (hx' ▸ (primaryComponentEquiv φ a).2)
  obtain ⟨z, hz⟩ := exists_form_self_div_two_eq_add_algebraMap hM φ hm
  rw [← hx, ← hx', discriminantQuadraticMap_mk, discriminantQuadraticMap_mk]
  refine Padic.addCircle_coe_eq_coe_of_eq_add_algebraMap (k := k + k')
    (n := p ^ k * c' - p ^ k' * c) ?_ hz
  push_cast
  linear_combination (p : ℚ) ^ k * hc' - (p : ℚ) ^ k' * hc

/-! ### The `p`-primary discriminant forms are local -/

/-- **The `p`-primary discriminant bilinear form is local.** An isometry `φ : L_p ≃ M_p` of the
localizations at `p` of two nondegenerate integral lattices induces an isometry between the
`p`-primary components of their discriminant bilinear modules. -/
noncomputable def primaryDiscriminantBilinearIsometry
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p)) :
    FiniteBilinearModule.Isometry
      (L.discriminantBilinearModule.restrict (primaryComponent L.discriminantBilinearModule p))
      (M.discriminantBilinearModule.restrict (primaryComponent M.discriminantBilinearModule p))
    where
  toAddEquiv := primaryComponentEquiv φ
  map_pairing' a b :=
    ((FiniteBilinearModule.restrict_pairing ..).trans <|
        (discriminantBilinearModule_pairing ..).trans
          (discriminantPairing_primaryComponentEquiv φ a b)).trans
      ((FiniteBilinearModule.restrict_pairing ..).trans
        (discriminantBilinearModule_pairing ..)).symm

/-- The isometry induced by `φ` matches representatives: if `x ∈ Lᵛ` represents a `p`-primary
class and `x' ∈ Mᵛ` represents its image, then `x'` and the image of `x` under the extension of
`φ` to the completed rational spaces differ by a vector of `M_p`. As the `p`-primary component
embeds in the discriminant group of `M_p`, this characterizes the isometry. -/
theorem localizationDualToCompletion_sub_mem_range_of_primaryDiscriminantBilinearIsometry
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p))
    {a : primaryComponent L.discriminantBilinearModule p} {x : L.dualCarrier}
    (hx : Submodule.Quotient.mk x = (a : L.discriminantBilinearModule)) {x' : M.dualCarrier}
    (hx' : Submodule.Quotient.mk x' =
      (primaryDiscriminantBilinearIsometry φ a : M.discriminantBilinearModule)) :
    M.localizationDualToCompletion p (1 ⊗ₜ x') -
        completedIsometryEquiv p φ (L.localizationDualToCompletion p (1 ⊗ₜ x)) ∈
      LinearMap.range (M.localizationToCompletion p) := by
  obtain ⟨m, hm⟩ := exists_one_tmul_eq_add φ hx hx'
  refine ⟨m, ?_⟩
  rw [hm, map_add, completedIsometryEquiv_localizationDualToCompletion,
    localizationDualToCompletion_localCarrierToDual, add_sub_cancel_left]

/-- **The `p`-primary discriminant quadratic form is local.** An isometry `φ : L_p ≃ M_p` of the
localizations at `p` of two even nondegenerate integral lattices induces an isometry between the
`p`-primary components of their discriminant quadratic modules. -/
noncomputable def primaryDiscriminantQuadraticIsometry (hL : L.IsEven) (hM : M.IsEven)
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p)) :
    FiniteQuadraticModule.Isometry
      ((L.discriminantQuadraticModule hL).restrict
        (primaryComponent (L.discriminantQuadraticModule hL) p))
      ((M.discriminantQuadraticModule hM).restrict
        (primaryComponent (M.discriminantQuadraticModule hM) p)) where
  toLinearEquiv := (primaryComponentEquiv φ).toIntLinearEquiv
  map_app' a :=
    ((FiniteQuadraticModule.restrict_quadratic ..).trans <|
        (discriminantQuadraticModule_quadratic ..).trans
          (discriminantQuadraticMap_primaryComponentEquiv hL hM φ a)).trans
      ((FiniteQuadraticModule.restrict_quadratic ..).trans
        (discriminantQuadraticModule_quadratic ..)).symm

/-- The quadratic and the bilinear isometries induced by `φ` act in the same way. -/
@[simp]
theorem primaryDiscriminantQuadraticIsometry_apply (hL : L.IsEven) (hM : M.IsEven)
    (φ : (L.localIntegralForm p).IsometryEquiv (M.localIntegralForm p))
    (a : primaryComponent (L.discriminantQuadraticModule hL) p) :
    (primaryDiscriminantQuadraticIsometry hL hM φ a).1 =
      (primaryDiscriminantBilinearIsometry φ a).1 :=
  (rfl)

/-! ### Discriminant forms are genus invariants -/

namespace SameGenus

/-- **Lattices in one genus have isometric discriminant bilinear forms.** This is the easy half of
Nikulin's Corollary 1.16.3: the genus of a nondegenerate lattice determines its discriminant
bilinear form `b_L`. -/
theorem nonempty_isometry_discriminantBilinearModule (h : L.SameGenus M) :
    Nonempty (FiniteBilinearModule.Isometry L.discriminantBilinearModule
      M.discriminantBilinearModule) :=
  FiniteBilinearModule.nonempty_isometry_of_forall_primaryComponent
    h.natCard_discriminantGroup_eq fun p hp ↦
      have : Fact p.Prime := ⟨hp⟩
      (h.localIntegralForm_equivalent p).map primaryDiscriminantBilinearIsometry

/-- **Even lattices in one genus have isometric discriminant quadratic forms.** This is the easy
half of Nikulin's Corollary 1.9.4: the genus of an even nondegenerate lattice determines its
discriminant quadratic form `q_L`. -/
theorem nonempty_isometry_discriminantQuadraticModule (h : L.SameGenus M) (hL : L.IsEven) :
    Nonempty (FiniteQuadraticModule.Isometry (L.discriminantQuadraticModule hL)
      (M.discriminantQuadraticModule (h.isEven_iff.mp hL))) :=
  FiniteQuadraticModule.nonempty_isometry_of_forall_primaryComponent
    h.natCard_discriminantGroup_eq fun p hp ↦
      have : Fact p.Prime := ⟨hp⟩
      (h.localIntegralForm_equivalent p).map
        (primaryDiscriminantQuadraticIsometry hL (h.isEven_iff.mp hL))

end SameGenus

end TauCeti.IntegralLattice
