/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.LinearAlgebra.Matrix.GeneralLinearGroup.Defs
public import Mathlib.NumberTheory.Padics.PadicIntegers
public import Mathlib.Topology.Algebra.OpenSubgroup
public import TauCeti.Topology.Algebra.Group.Profinite.ZHat.Units
public import TauCeti.Topology.Algebra.Group.Units
public import TauCeti.Topology.Instances.Matrix
import TauCeti.Data.ZMod.Divisibility
import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Map
import TauCeti.NumberTheory.ModularForms.CongruenceSubgroups.LevelSubgroup
import TauCeti.Topology.Algebra.Group.Profinite.Basic

/-!
# The profinite group `GL₂(ℤ̂)`

The profinite general linear group `GL₂(ℤ̂)` is `GL (Fin 2) (Additive zHat.{0})`, where
`Additive zHat` is the ring of profinite integers. Because `Additive zHat` is a compact, totally
disconnected topological commutative ring, entrywise product and unit topologies make `GL₂(ℤ̂)` a
compact, totally disconnected, Hausdorff topological group.

Entrywise reduction modulo `n : ℕ+` gives continuous surjective group homomorphisms
`GL2Zhat.red n : GL2Zhat →* GL (Fin 2) (ZMod n)`, whose kernels are the open normal principal
congruence subgroups `GL2Zhat.Gamma n`. These reductions separate points and identify `GL₂(ℤ̂)` as
the inverse limit of the finite groups `GL₂(ℤ / n)`. Every open subgroup of `GL₂(ℤ̂)` contains some
`Gamma n`.

The Chinese remainder decomposition `Additive zHat ≃+* ∀ ℓ : Nat.Primes, ℤ_[ℓ]` induces a
topological group isomorphism
`GL2Zhat.piPadicEquiv : GL2Zhat ≃ₜ* ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]`, yielding continuous open
surjective `ℓ`-adic projections `GL2Zhat.proj ℓ` and the join identity
`Gamma m ⊔ Gamma n = Gamma (gcd m n)`.

## Main definitions

* `TauCeti.GL2Zhat`: the profinite group `GL (Fin 2) (Additive zHat.{0})`.
* `TauCeti.GL2Zhat.red`: reduction modulo `n : ℕ+`, `GL2Zhat →* GL (Fin 2) (ZMod n)`.
* `TauCeti.GL2Zhat.Gamma`: the principal congruence subgroup `ker (red n) : OpenSubgroup GL2Zhat`.
* `TauCeti.GL2Zhat.SL2Zhat`: the closed normal subgroup `ker det : Subgroup GL2Zhat`.
* `TauCeti.GL2Zhat.proj`: the `ℓ`-adic projection `GL2Zhat →* GL (Fin 2) ℤ_[ℓ]`.
* `TauCeti.GL2Zhat.piPadicEquiv`: the topological group isomorphism
  `GL2Zhat ≃ₜ* ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]`.

## Main results

* `TauCeti.GL2Zhat.red_surjective`: reduction modulo every `n : ℕ+` is surjective.
* `TauCeti.GL2Zhat.red_ext`, `TauCeti.GL2Zhat.continuous_iff_forall_continuous_red`,
  `TauCeti.GL2Zhat.existsUnique_forall_red_eq`: inverse-limit properties of `GL₂(ℤ̂)`.
* `TauCeti.GL2Zhat.Gamma_le_Gamma_iff`, `TauCeti.GL2Zhat.Gamma_lcm_eq_inf`,
  `TauCeti.GL2Zhat.Gamma_gcd_eq_sup`: lattice and divisibility laws for `Gamma`.
* `TauCeti.GL2Zhat.exists_Gamma_le`: every open subgroup of `GL₂(ℤ̂)` contains some `Gamma n`.
* `TauCeti.GL2Zhat.isOpenMap_proj`, `TauCeti.GL2Zhat.proj_surjective`: each `ℓ`-adic projection
  is open and surjective.
* `TauCeti.GL2Zhat.index_Gamma`: `[GL₂(ℤ̂) : Gamma n] = |GL₂(ℤ / n)|`.

## References

* D. Zywina, *On the possible images of the mod `ℓ` representations associated to elliptic curves
  over `ℚ`*, arXiv:1508.07660, §3.
-/

public section

namespace TauCeti

open Matrix

/-- The profinite group `GL₂(ℤ̂) = GL (Fin 2) (Additive zHat.{0})`. -/
abbrev GL2Zhat : Type := GL (Fin 2) (Additive zHat.{0})

namespace GL2Zhat

private theorem continuous_glMap {R S : Type*} [CommRing R] [CommRing S]
    [TopologicalSpace R] [TopologicalSpace S] {f : R →+* S} (hf : Continuous f) :
    Continuous (GeneralLinearGroup.map (n := Fin 2) f) := by
  rw [Units.continuous_iff]
  refine ⟨continuous_matrix fun i j ↦ hf.comp ?_, continuous_matrix fun i j ↦ hf.comp ?_⟩
  · exact (Units.continuous_val (M := Matrix (Fin 2) (Fin 2) R)).matrix_elem i j
  · exact (Units.continuous_coe_inv (M := Matrix (Fin 2) (Fin 2) R)).matrix_elem i j

section Reduction

/-- Reduction modulo `n : ℕ+`, given by entrywise reduction `zHat.toZMod n`. -/
noncomputable def red (n : ℕ+) : GL2Zhat →* GL (Fin 2) (ZMod n) :=
  GeneralLinearGroup.map (zHat.toZMod n)

@[simp]
theorem red_apply (n : ℕ+) (g : GL2Zhat) (i j : Fin 2) :
    (red n g : Matrix (Fin 2) (Fin 2) (ZMod n)) i j =
      zHat.toZMod n ((g : Matrix (Fin 2) (Fin 2) (Additive zHat.{0})) i j) := by
  simp [red]

/-- Reduction modulo `n` commutes with negation. -/
@[simp]
theorem red_neg (n : ℕ+) (g : GL2Zhat) : red n (-g) = -red n g :=
  GeneralLinearGroup.map_neg _ g

/-- Reduction modulo `n` is continuous. -/
@[continuity, fun_prop]
theorem continuous_red (n : ℕ+) : Continuous (red n) :=
  continuous_glMap (zHat.continuous_toZMod n)

/-- Reduction modulo `n : ℕ+` is surjective onto `GL₂(ℤ / n)`. -/
theorem red_surjective (n : ℕ+) : Function.Surjective (red n) := fun g ↦ by
  obtain ⟨u, hu⟩ := zHat.unitsMap_toZMod_surjective.{0} n g.det
  let dg : GL (Fin 2) (ZMod n) :=
    GeneralLinearGroup.mk'' !![(g.det : ZMod n), 0; 0, 1] (by simp [Matrix.det_fin_two_of])
  let du : GL2Zhat :=
    GeneralLinearGroup.mk'' !![(u : Additive zHat.{0}), 0; 0, 1] (by simp [Matrix.det_fin_two_of])
  let s := g * dg⁻¹
  have hs : s ∈ (GeneralLinearGroup.det : GL (Fin 2) (ZMod n) →* _).ker := by
    rw [MonoidHom.mem_ker, map_mul, map_inv]
    have hdet : GeneralLinearGroup.det dg = g.det := by
      apply Units.ext
      simp [dg, Matrix.det_fin_two_of]
    rw [hdet, mul_inv_cancel]
  obtain ⟨γ, hγ⟩ := (TauCeti.range_mapGL_zmod n).ge hs
  have hγ_red : red n (SpecialLinearGroup.mapGL (Additive zHat.{0}) γ) = s := by
    rw [← hγ]
    ext i j
    simp [SpecialLinearGroup.mapGL_coe_matrix, map_intCast]
  have hu_red : red n du = dg := by
    have hu' : zHat.toZMod n (u : Additive zHat.{0}) =
        (g : Matrix (Fin 2) (Fin 2) (ZMod n)).det := by
      have hval := congrArg Units.val hu
      simpa [Units.coe_map] using hval
    ext i j
    fin_cases i <;> fin_cases j <;> simp [du, dg, hu']
  refine ⟨SpecialLinearGroup.mapGL (Additive zHat.{0}) γ * du, ?_⟩
  rw [map_mul, hγ_red, hu_red, inv_mul_cancel_right]

/-- Compatibility of reductions along divisibility. -/
@[simp]
theorem map_castHom_red {m n : ℕ+} (h : (m : ℕ) ∣ n) (g : GL2Zhat) :
    GeneralLinearGroup.map (ZMod.castHom h (ZMod m)) (red n g) = red m g := by
  ext i j
  simp [zHat.cast_toZMod h]

/-- Compatibility of reductions along divisibility, as an equality of group homomorphisms. -/
theorem map_castHom_comp_red {m n : ℕ+} (h : (m : ℕ) ∣ n) :
    (GeneralLinearGroup.map (ZMod.castHom h (ZMod m))).comp (red n) = red m :=
  MonoidHom.ext (map_castHom_red h)

/-- An element of `GL₂(ℤ̂)` is determined by its reductions modulo every `n : ℕ+`. -/
@[ext (iff := false)]
theorem red_ext {g₁ g₂ : GL2Zhat} (h : ∀ n : ℕ+, red n g₁ = red n g₂) : g₁ = g₂ := by
  apply Units.ext
  apply Matrix.ext
  intro i j
  exact zHat.ext_of_toZMod fun n ↦ by
    have hn := congrArg (fun x : GL (Fin 2) (ZMod n) ↦ (x : Matrix (Fin 2) (Fin 2) (ZMod n)) i j)
      (h n)
    simpa [red_apply] using hn

/-- Two elements of `GL₂(ℤ̂)` are equal iff all their finite-level reductions agree. -/
theorem red_ext_iff {g₁ g₂ : GL2Zhat} : g₁ = g₂ ↔ ∀ n : ℕ+, red n g₁ = red n g₂ :=
  ⟨fun h _ ↦ h ▸ rfl, red_ext⟩

/-- Continuity into `GL₂(ℤ̂)` is detected by the finite-level reductions. -/
theorem continuous_iff_forall_continuous_red {X : Type*} [TopologicalSpace X] {f : X → GL2Zhat} :
    Continuous f ↔ ∀ n : ℕ+, Continuous fun x ↦ red n (f x) := by
  refine ⟨fun hf n ↦ (continuous_red n).comp hf, fun h ↦ ?_⟩
  rw [Units.continuous_iff]
  refine ⟨continuous_matrix fun i j ↦ zHat.continuous_iff_forall_continuous_toZMod.mpr fun n ↦ ?_,
    continuous_matrix fun i j ↦ zHat.continuous_iff_forall_continuous_toZMod.mpr fun n ↦ ?_⟩
  · exact (Units.continuous_val.comp (h n)).matrix_elem i j
  · have hinv : (fun x ↦ zHat.toZMod n (((f x)⁻¹ : GL2Zhat).val i j)) =
        fun x ↦ (((red n (f x))⁻¹ : GL (Fin 2) (ZMod n)).val i j) := by
      ext x
      rw [← map_inv (red n), ← red_apply]
    rw [hinv]
    exact (Units.continuous_val.comp (h n).inv).matrix_elem i j

/-- **Inverse limit property of `GL₂(ℤ̂)`.** A compatible family of elements in `GL₂(ℤ / n)`
lifts uniquely to `GL₂(ℤ̂)`. -/
theorem existsUnique_forall_red_eq (g : ∀ n : ℕ+, GL (Fin 2) (ZMod n))
    (hg : ∀ (m n : ℕ+) (h : (m : ℕ) ∣ n),
      GeneralLinearGroup.map (ZMod.castHom h (ZMod m)) (g n) = g m) :
    ∃! a : GL2Zhat, ∀ n : ℕ+, red n a = g n := by
  have hentry (i j : Fin 2) : ∃! x : Additive zHat.{0},
      ∀ n : ℕ+, zHat.toZMod n x = (g n : Matrix (Fin 2) (Fin 2) (ZMod n)) i j :=
    zHat.existsUnique_forall_toZMod_eq (fun n ↦ (g n : Matrix (Fin 2) (Fin 2) (ZMod n)) i j)
      fun m n h ↦ by
        simpa using congrArg
          (fun y : GL (Fin 2) (ZMod m) ↦ (y : Matrix (Fin 2) (Fin 2) (ZMod m)) i j) (hg m n h)
  choose A hA _ using hentry
  have hunit : IsUnit (Matrix.of A).det := by
    rw [zHat.isUnit_iff_toZMod]
    intro n
    rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have hmat : (Matrix.of A).map (zHat.toZMod n) = (g n : Matrix (Fin 2) (Fin 2) (ZMod n)) := by
      ext i j
      exact hA i j n
    rw [hmat]
    exact Matrix.isUnits_det_units (g n)
  refine ⟨GeneralLinearGroup.mk'' (Matrix.of A) hunit, fun n ↦ ?_, fun b hb ↦ red_ext fun n ↦ ?_⟩
  · ext i j
    exact hA i j n
  · rw [hb n]
    ext i j
    exact (hA i j n).symm

end Reduction

section CongruenceSubgroups

/-- The principal congruence subgroup of level `n : ℕ+`, `ker (red n) : OpenSubgroup GL2Zhat`. -/
noncomputable def Gamma (n : ℕ+) : OpenSubgroup GL2Zhat where
  toSubgroup := (red n).ker
  isOpen' := (isOpen_discrete {1}).preimage (continuous_red n)

@[simp]
theorem mem_Gamma_iff (n : ℕ+) (g : GL2Zhat) : g ∈ Gamma n ↔ red n g = 1 :=
  Iff.rfl

instance normal_Gamma (n : ℕ+) : (Gamma n).toSubgroup.Normal :=
  (red n).normal_ker

/-- `Gamma 1` is the whole group `GL₂(ℤ̂)`. -/
@[simp]
theorem Gamma_one : Gamma 1 = ⊤ :=
  OpenSubgroup.ext fun g ↦ by
    simp only [mem_Gamma_iff, OpenSubgroup.mem_top, iff_true]
    ext i j
    simp only [PNat.one_coe]
    exact Subsingleton.elim _ _

/-- `Gamma n ≤ Gamma m` whenever `m ∣ n`. -/
theorem Gamma_le_Gamma_of_dvd {m n : ℕ+} (h : (m : ℕ) ∣ n) : Gamma n ≤ Gamma m := by
  intro g hg
  rw [mem_Gamma_iff, ← map_castHom_red h, hg, map_one]

/-- Divisibility characterization of inclusions among principal congruence subgroups:
`Gamma n ≤ Gamma m ↔ m ∣ n`. -/
theorem Gamma_le_Gamma_iff {m n : ℕ+} : Gamma n ≤ Gamma m ↔ (m : ℕ) ∣ n := by
  refine ⟨fun h ↦ ?_, Gamma_le_Gamma_of_dvd⟩
  let g : GL2Zhat := GeneralLinearGroup.mk'' !![1, (n : Additive zHat.{0}); 0, 1]
    (by simp [Matrix.det_fin_two_of])
  have hgn : g ∈ Gamma n := by
    rw [mem_Gamma_iff]
    ext i j
    fin_cases i <;> fin_cases j <;> simp [g]
  have hgm := congrArg
    (fun x : GL (Fin 2) (ZMod m) ↦ (x : Matrix (Fin 2) (Fin 2) (ZMod m)) 0 1)
    ((mem_Gamma_iff m g).mp (h hgn))
  simpa [g, ZMod.natCast_eq_zero_iff] using hgm

private theorem mem_Gamma_of_forall_prime_pow {n : ℕ+} {g : GL2Zhat}
    (h : ∀ (p k : ℕ) (hp : p.Prime), p ^ k ∣ n →
      red ⟨p ^ k, pow_pos hp.pos k⟩ g = 1) : g ∈ Gamma n := by
  rw [mem_Gamma_iff]
  ext i j
  refine ZMod.eq_of_forall_cast_eq_of_prime_pow_dvd fun p k hp _ hpk ↦ ?_
  let q : ℕ+ := ⟨p ^ k, pow_pos hp.pos k⟩
  have hq : red q g = 1 := h p k hp hpk
  have hq_ij := congrArg
    (fun x : GL (Fin 2) (ZMod q) ↦ (x : Matrix (Fin 2) (Fin 2) (ZMod q)) i j)
    ((map_castHom_red (m := q) (n := n) hpk g).trans hq)
  have hcast_lhs : (((red n g : GL (Fin 2) (ZMod n)) : Matrix (Fin 2) (Fin 2) (ZMod n)) i j).cast =
      (GeneralLinearGroup.map (ZMod.castHom hpk (ZMod q)) (red n g) :
        Matrix (Fin 2) (Fin 2) (ZMod q)) i j := by
    simp only [GeneralLinearGroup.map_apply, red_apply]
    exact (ZMod.castHom_apply (R := ZMod ↑q) (h := hpk) _).symm
  have hcast_rhs : (((1 : GL (Fin 2) (ZMod n)) : Matrix (Fin 2) (Fin 2) (ZMod n)) i j).cast =
      ((1 : GL (Fin 2) (ZMod q)) : Matrix (Fin 2) (Fin 2) (ZMod q)) i j := by
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs
    · exact ((ZMod.castHom_apply (1 : ZMod n)).symm).trans (map_one (ZMod.castHom hpk (ZMod q)))
    · exact ZMod.cast_zero
  exact hcast_lhs.trans (hq_ij.trans hcast_rhs.symm)

/-- The intersection of `Gamma m` and `Gamma n` is `Gamma (lcm m n)`. -/
theorem Gamma_lcm_eq_inf (m n : ℕ+) :
    Gamma ⟨Nat.lcm m n, Nat.lcm_pos m.pos n.pos⟩ = Gamma m ⊓ Gamma n := by
  apply le_antisymm
  · exact le_inf (Gamma_le_Gamma_of_dvd (Nat.dvd_lcm_left _ _))
      (Gamma_le_Gamma_of_dvd (Nat.dvd_lcm_right _ _))
  · intro g hg
    refine mem_Gamma_of_forall_prime_pow fun p k hp hpk ↦ ?_
    have hle : k ≤ (Nat.lcm m n).factorization p :=
      (hp.pow_dvd_iff_le_factorization (Nat.lcm_ne_zero m.ne_zero n.ne_zero)).mp hpk
    rw [Nat.factorization_lcm m.ne_zero n.ne_zero, Finsupp.sup_apply, le_max_iff] at hle
    rcases hle with hm | hn
    · exact Gamma_le_Gamma_of_dvd ((hp.pow_dvd_iff_le_factorization m.ne_zero).mpr hm) hg.1
    · exact Gamma_le_Gamma_of_dvd ((hp.pow_dvd_iff_le_factorization n.ne_zero).mpr hn) hg.2

/-- The principal congruence subgroups intersect to the trivial subgroup. -/
theorem iInf_Gamma_eq_bot : (⨅ n : ℕ+, (Gamma n).toSubgroup) = ⊥ := by
  ext g
  simp [Subgroup.mem_iInf, red_ext_iff]

/-- **Every open subgroup of `GL₂(ℤ̂)` contains a principal congruence subgroup `Gamma n`.** -/
theorem exists_Gamma_le (H : OpenSubgroup GL2Zhat) : ∃ n : ℕ+, Gamma n ≤ H := by
  have hclosed : ∀ n : ℕ+, IsClosed ((Gamma n).toSubgroup : Set GL2Zhat) :=
    fun n ↦ (Gamma n).isClosed
  have hdir : Directed (· ≥ ·) fun n : ℕ+ ↦ (Gamma n).toSubgroup := fun m n ↦
    ⟨m * n,
      Gamma_le_Gamma_of_dvd (PNat.mul_coe m n ▸ dvd_mul_right (m : ℕ) n),
      Gamma_le_Gamma_of_dvd (PNat.mul_coe m n ▸ dvd_mul_left (n : ℕ) m)⟩
  have hinf : (⨅ n : ℕ+, (Gamma n).toSubgroup) ≤ H.toSubgroup := by
    rw [iInf_Gamma_eq_bot]
    exact bot_le
  exact Subgroup.exists_le_of_iInf_le_of_directed hclosed hdir H.isOpen hinf

/-- The quotient `GL₂(ℤ̂) ⧸ Gamma n` is canonically isomorphic to `GL₂(ℤ / n)`. -/
noncomputable def quotientGammaEquiv (n : ℕ+) :
    GL2Zhat ⧸ (Gamma n).toSubgroup ≃* GL (Fin 2) (ZMod n) :=
  QuotientGroup.quotientKerEquivOfSurjective (red n) (red_surjective n)

/-- The index of `Gamma n` in `GL₂(ℤ̂)` is `|GL₂(ℤ / n)|`. -/
theorem index_Gamma (n : ℕ+) :
    (Gamma n).toSubgroup.index = Nat.card (GL (Fin 2) (ZMod n)) := by
  rw [Subgroup.index_eq_card, Nat.card_congr (quotientGammaEquiv n).toEquiv]

end CongruenceSubgroups

section DeterminantAndSL2

/-- The determinant homomorphism `GL₂(ℤ̂) →* ℤ̂ˣ` is surjective. -/
theorem det_surjective :
    Function.Surjective (GeneralLinearGroup.det : GL2Zhat →* (Additive zHat.{0})ˣ) :=
  GeneralLinearGroup.det_surjective

/-- The determinant homomorphism `GL₂(ℤ̂) →* ℤ̂ˣ` is continuous. -/
@[continuity, fun_prop]
theorem continuous_det :
    Continuous (GeneralLinearGroup.det : GL2Zhat →* (Additive zHat.{0})ˣ) := by
  rw [Units.continuous_iff]
  refine ⟨Continuous.matrix_det Units.continuous_val, ?_⟩
  exact Continuous.matrix_det Units.continuous_coe_inv

/-- Reduction modulo `n` intertwines determinants. -/
@[simp]
theorem map_toZMod_det (n : ℕ+) (g : GL2Zhat) :
    Units.map (zHat.toZMod n : Additive zHat.{0} →* ZMod n) (GeneralLinearGroup.det g) =
      GeneralLinearGroup.det (red n g) :=
  (GeneralLinearGroup.map_det (zHat.toZMod n) g).symm

/-- `SL₂(ℤ̂)`, the kernel of the determinant homomorphism on `GL₂(ℤ̂)`. -/
noncomputable def SL2Zhat : Subgroup GL2Zhat :=
  (GeneralLinearGroup.det : GL2Zhat →* (Additive zHat.{0})ˣ).ker

@[simp]
theorem mem_SL2Zhat_iff (g : GL2Zhat) : g ∈ SL2Zhat ↔ GeneralLinearGroup.det g = 1 :=
  Iff.rfl

/-- `SL₂(ℤ̂)` is a closed subgroup of `GL₂(ℤ̂)`. -/
theorem isClosed_SL2Zhat : IsClosed (SL2Zhat : Set GL2Zhat) :=
  isClosed_singleton.preimage continuous_det

instance normal_SL2Zhat : SL2Zhat.Normal :=
  (GeneralLinearGroup.det : GL2Zhat →* (Additive zHat.{0})ˣ).normal_ker

end DeterminantAndSL2

section ProductDecomposition

/-- The `ℓ`-adic projection `GL₂(ℤ̂) →* GL₂(ℤ_ℓ)` induced by `zHat.component ℓ`. -/
noncomputable def proj (ℓ : Nat.Primes) : GL2Zhat →* GL (Fin 2) ℤ_[ℓ] :=
  GeneralLinearGroup.map (zHat.component ℓ)

@[simp]
theorem proj_apply (ℓ : Nat.Primes) (g : GL2Zhat) (i j : Fin 2) :
    (proj ℓ g : Matrix (Fin 2) (Fin 2) ℤ_[ℓ]) i j =
      zHat.component ℓ ((g : Matrix (Fin 2) (Fin 2) (Additive zHat.{0})) i j) := by
  simp [proj]

/-- Each `ℓ`-adic projection is continuous. -/
@[continuity, fun_prop]
theorem continuous_proj (ℓ : Nat.Primes) : Continuous (proj ℓ) :=
  continuous_glMap (zHat.continuous_component ℓ)

/-- **Product decomposition of `GL₂(ℤ̂)`.** The Chinese remainder decomposition of `ℤ̂` induces a
topological group isomorphism `GL₂(ℤ̂) ≃ₜ* ∀ ℓ : Nat.Primes, GL₂(ℤ_ℓ)`. -/
noncomputable def piPadicEquiv : GL2Zhat ≃ₜ* ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ] :=
  let e : GL2Zhat ≃* ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ] :=
    (GeneralLinearGroup.mapEquiv (Fin 2) zHat.ringEquivPiPadicInt.{0}).trans
      (GeneralLinearGroup.piEquiv _)
  have hcont : Continuous e := by
    refine continuous_pi fun ℓ ↦ (continuous_proj ℓ).congr fun g ↦ ?_
    ext i j
    simp [e, zHat.ringEquivPiPadicInt_apply]
  ContinuousMulEquiv.mk e hcont (hcont.continuous_symm_of_equiv_compact_to_t2 (f := e.toEquiv))

@[simp]
theorem piPadicEquiv_apply (g : GL2Zhat) (ℓ : Nat.Primes) :
    piPadicEquiv g ℓ = proj ℓ g := by
  ext i j
  simp [piPadicEquiv, zHat.ringEquivPiPadicInt_apply]

@[simp]
theorem proj_piPadicEquiv_symm (f : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ]) (ℓ : Nat.Primes) :
    proj ℓ (piPadicEquiv.symm f) = f ℓ := by
  rw [← piPadicEquiv_apply]
  exact congrFun (piPadicEquiv.apply_symm_apply f) ℓ

/-- Each `ℓ`-adic projection is surjective. -/
theorem proj_surjective (ℓ : Nat.Primes) : Function.Surjective (proj ℓ) := fun A ↦ by
  classical
  refine ⟨piPadicEquiv.symm (fun q ↦ if h : q = ℓ then h ▸ A else 1), ?_⟩
  simp

/-- Each `ℓ`-adic projection is an open map. -/
theorem isOpenMap_proj (ℓ : Nat.Primes) : IsOpenMap (proj ℓ) := by
  have h : (proj ℓ : GL2Zhat → GL (Fin 2) ℤ_[ℓ]) = Function.eval ℓ ∘ piPadicEquiv :=
    funext fun g ↦ (piPadicEquiv_apply g ℓ).symm
  rw [h]
  exact (isOpenMap_eval ℓ).comp piPadicEquiv.toHomeomorph.isOpenMap

/-- Reducing the `ℓ`-adic projection modulo `ℓ ^ k` agrees with `red (ℓ ^ k)`. -/
theorem map_toZModPow_proj (ℓ : Nat.Primes) (k : ℕ) (g : GL2Zhat) :
    GeneralLinearGroup.map (PadicInt.toZModPow k) (proj ℓ g) =
      red ⟨(ℓ : ℕ) ^ k, pow_pos ℓ.property.pos k⟩ g := by
  ext i j
  simp only [GeneralLinearGroup.map_apply, proj, red, zHat.toZModPow_component]
  rfl

/-- Membership in `Gamma n` is checked prime-power by prime-power on the `ℓ`-adic projections. -/
theorem mem_Gamma_iff_forall_proj {n : ℕ+} {g : GL2Zhat} :
    g ∈ Gamma n ↔ ∀ ℓ : Nat.Primes,
      GeneralLinearGroup.map (PadicInt.toZModPow ((n : ℕ).factorization ℓ)) (proj ℓ g) = 1 := by
  constructor
  · intro hg ℓ
    rw [map_toZModPow_proj]
    have hdvd : (ℓ : ℕ) ^ (n : ℕ).factorization ℓ ∣ n :=
      Nat.ordProj_dvd n ℓ
    exact (mem_Gamma_iff _ g).mp (Gamma_le_Gamma_of_dvd hdvd hg)
  · intro h
    refine mem_Gamma_of_forall_prime_pow fun p k hp hpk ↦ ?_
    have hle : k ≤ (n : ℕ).factorization p :=
      (hp.pow_dvd_iff_le_factorization n.ne_zero).mp hpk
    have : Fact p.Prime := ⟨hp⟩
    let ℓ : Nat.Primes := ⟨p, hp⟩
    let m : ℕ+ := ⟨p ^ (n : ℕ).factorization p, pow_pos hp.pos _⟩
    let q : ℕ+ := ⟨p ^ k, pow_pos hp.pos k⟩
    have hm_eq : GeneralLinearGroup.map (PadicInt.toZModPow ((n : ℕ).factorization ℓ))
        (proj ℓ g) = red m g :=
      map_toZModPow_proj ℓ ((n : ℕ).factorization ℓ) g
    have hm1 : red m g = 1 := hm_eq.symm.trans (h ℓ)
    have hqm : (q : ℕ) ∣ m := pow_dvd_pow p hle
    rw [← map_castHom_red hqm g, hm1, map_one]

/-- **Join law for principal congruence subgroups:** `Gamma m ⊔ Gamma n = Gamma (gcd m n)`. -/
theorem Gamma_gcd_eq_sup (m n : ℕ+) :
    Gamma m ⊔ Gamma n = Gamma ⟨Nat.gcd m n, Nat.gcd_pos_of_pos_left n m.pos⟩ := by
  classical
  let d : ℕ+ := ⟨Nat.gcd m n, Nat.gcd_pos_of_pos_left n m.pos⟩
  have hd : (d : ℕ) = Nat.gcd m n := rfl
  refine le_antisymm
    (sup_le (Gamma_le_Gamma_of_dvd (Nat.gcd_dvd_left _ _))
      (Gamma_le_Gamma_of_dvd (Nat.gcd_dvd_right _ _)))
    fun g hg ↦ ?_
  let a : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ] := fun ℓ ↦
    if (m : ℕ).factorization ℓ ≤ (n : ℕ).factorization ℓ then proj ℓ g else 1
  let b : ∀ ℓ : Nat.Primes, GL (Fin 2) ℤ_[ℓ] := fun ℓ ↦
    if (m : ℕ).factorization ℓ ≤ (n : ℕ).factorization ℓ then 1 else proj ℓ g
  have hmul : piPadicEquiv.symm a * piPadicEquiv.symm b = g := by
    apply piPadicEquiv.injective
    ext ℓ i j
    simp only [map_mul, piPadicEquiv_apply, proj_piPadicEquiv_symm, a, b]
    split_ifs <;> simp
  have ha : piPadicEquiv.symm a ∈ Gamma m := by
    rw [mem_Gamma_iff_forall_proj]
    intro ℓ
    rw [proj_piPadicEquiv_symm]
    dsimp only [a]
    split_ifs with hle
    · have hfac : (d : ℕ).factorization ℓ = (m : ℕ).factorization ℓ := by
        rw [hd, Nat.factorization_gcd m.ne_zero n.ne_zero]
        exact min_eq_left hle
      have hgℓ := mem_Gamma_iff_forall_proj.mp (hg : g ∈ Gamma d) ℓ
      rwa [hfac] at hgℓ
    · simp
  have hb : piPadicEquiv.symm b ∈ Gamma n := by
    rw [mem_Gamma_iff_forall_proj]
    intro ℓ
    rw [proj_piPadicEquiv_symm]
    dsimp only [b]
    split_ifs with hle
    · simp
    · have hfac : (d : ℕ).factorization ℓ = (n : ℕ).factorization ℓ := by
        rw [hd, Nat.factorization_gcd m.ne_zero n.ne_zero]
        exact min_eq_right (le_of_not_ge hle)
      have hgℓ := mem_Gamma_iff_forall_proj.mp (hg : g ∈ Gamma d) ℓ
      rwa [hfac] at hgℓ
  rw [← hmul]
  exact Subgroup.mul_mem_sup ha hb

end ProductDecomposition

end GL2Zhat

end TauCeti
