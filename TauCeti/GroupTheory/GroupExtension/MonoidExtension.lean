/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Group.Int.Defs
public import Mathlib.GroupTheory.GroupAction.ConjAct
public import Mathlib.GroupTheory.QuotientGroup.Defs
public import Mathlib.GroupTheory.Subgroup.Centralizer
import Mathlib.GroupTheory.GroupAction.Quotient
import Mathlib.Tactic.Group
import TauCeti.Algebra.Group.Subgroup.Ker
import TauCeti.Algebra.Group.Subgroup.Map
import TauCeti.GroupTheory.Coset.Fiber
import TauCeti.GroupTheory.GroupAction.Quotient

/-!
# Nonnegative monoid extensions of groups over `ℤ`

Given `deg : Γtilde →* Multiplicative ℤ` and `ι : G →* Γtilde` with `ι.range = deg.ker` (without
assuming `deg` surjective), this file develops the pure group-theoretic infrastructure for the
nonnegative submonoid `Γ = deg⁻¹(ℕ)`:

* `TauCeti.MonoidExtension.nonnegSubmonoid` and `TauCeti.MonoidExtension.toNonnegSubmonoid`:
  `Γ = { γ : Γtilde | 0 ≤ toAdd (deg γ) }` and `G →* Γ`.
* `TauCeti.MonoidExtension.centralizerSubgroup`, `TauCeti.MonoidExtension.conjAut`,
  `TauCeti.MonoidExtension.conjNonneg`, `TauCeti.MonoidExtension.conjCentralizerEquiv`:
  centralizers `Z_γ ≤ G`, conjugation automorphisms of `G`, and `G`-conjugation on `Γ`.
* `TauCeti.MonoidExtension.DegreeFiber`, `TauCeti.MonoidExtension.ConjClasses`: degree-`d` fibers
  in `Γ` and their `G`-conjugacy classes (finite when `G` is finite).
* `TauCeti.MonoidExtension.degreeFiberEquivGroup`, `TauCeti.MonoidExtension.orbitStabilizerEquiv`:
  torsor identification `DegreeFiber deg d ≃ G` and orbit-stabilizer decomposition into
  `G`-conjugacy classes and centralizer cosets.

## References

* The Stacks Project, Section 64.15 (Lemmas 64.15.4 and 64.15.5);
  P. Deligne, *Cohomologie étale* (SGA 4½), `[Rapport]`, §3.
-/

public section
noncomputable section

namespace TauCeti.MonoidExtension

/-- The submonoid `Γ = deg⁻¹(ℕ) = { γ : Γtilde | 0 ≤ toAdd (deg γ) }` of nonnegative-degree
elements in `Γtilde`. -/
def nonnegSubmonoid {Γtilde : Type*} [Monoid Γtilde] (deg : Γtilde →* Multiplicative ℤ) :
    Submonoid Γtilde where
  carrier := { γ : Γtilde | 0 ≤ Multiplicative.toAdd (deg γ) }
  one_mem' := by simp
  mul_mem' ha hb := by simp only [Set.mem_ofPred_eq, map_mul, toAdd_mul] at ha hb ⊢; omega

@[simp] theorem mem_nonnegSubmonoid {Γtilde : Type*} [Monoid Γtilde]
    {deg : Γtilde →* Multiplicative ℤ} {γ : Γtilde} :
    γ ∈ nonnegSubmonoid deg ↔ 0 ≤ Multiplicative.toAdd (deg γ) := by rfl

variable {G Γtilde : Type*} [Group G] [Group Γtilde]

/-- The centralizer subgroup `Z_γ = { g ∈ G | ι g * γ = γ * ι g } ≤ G`. -/
def centralizerSubgroup (ι : G →* Γtilde) (γ : Γtilde) : Subgroup G :=
  (Subgroup.centralizer {γ}).comap ι

@[simp] theorem mem_centralizerSubgroup {ι : G →* Γtilde} {γ : Γtilde} {g : G} :
    g ∈ centralizerSubgroup ι γ ↔ ι g * γ = γ * ι g := Subgroup.mem_centralizer_singleton_iff

section ExtensionMaps
variable (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)

/-- Inclusion of the kernel subgroup `G` into `nonnegSubmonoid deg`. -/
def toNonnegSubmonoid (hker : ι.range = deg.ker) : G →* nonnegSubmonoid deg :=
  ι.codRestrict (nonnegSubmonoid deg) fun g ↦ by
    simp [MonoidHom.mem_ker.1 (hker ▸ MonoidHom.mem_range.2 ⟨g, rfl⟩)]

@[simp] theorem coe_toNonnegSubmonoid (hker : ι.range = deg.ker) (g : G) :
    (toNonnegSubmonoid ι deg hker g : Γtilde) = ι g := by rfl

section ConjAut
variable (hι : Function.Injective ι) (hker : ι.range = deg.ker)

/-- Conjugation by `γ : Γtilde` on `G` across `1 → G → Γtilde → ℤ`. -/
def conjAut (γ : Γtilde) : G ≃* G :=
  have : ι.range.Normal := hker ▸ deg.normal_ker
  (MonoidHom.ofInjective hι).trans <| (MulAut.conjNormal γ).trans (MonoidHom.ofInjective hι).symm

@[simp] theorem apply_conjAut (γ : Γtilde) (g : G) :
    ι (conjAut ι deg hι hker γ g) = γ * ι g * γ⁻¹ := by
  have : ι.range.Normal := hker ▸ deg.normal_ker
  simp [conjAut, MonoidHom.apply_ofInjective_symm, MulAut.conjNormal_apply,
    MonoidHom.ofInjective_apply]

@[simp] theorem conjAut_one : conjAut ι deg hι hker 1 = MulEquiv.refl G := by
  ext g; exact hι (by simp)
@[simp] theorem conjAut_mul (γ₁ γ₂ : Γtilde) :
    conjAut ι deg hι hker (γ₁ * γ₂) =
      (conjAut ι deg hι hker γ₂).trans (conjAut ι deg hι hker γ₁) := by
  ext g; exact hι (by simp [mul_assoc])
@[simp] theorem conjAut_symm (γ : Γtilde) :
    (conjAut ι deg hι hker γ).symm = conjAut ι deg hι hker γ⁻¹ := by
  ext g; exact (conjAut ι deg hι hker γ).injective <| hι (by simp [mul_assoc])
@[simp] theorem conjAut_map (k : G) : conjAut ι deg hι hker (ι k) = MulAut.conj k := by
  ext g; exact hι (by simp)

/-- Fixed points of `conjAut` on `G` are precisely `centralizerSubgroup ι γ`. -/
theorem eqLocus_conjAut (γ : Γtilde) :
    (conjAut ι deg hι hker γ).toMonoidHom.eqLocus (.id G) = centralizerSubgroup ι γ := by
  ext g; rw [MonoidHom.mem_eqLocus, MulEquiv.coe_toMonoidHom, MonoidHom.id_apply, ← hι.eq_iff,
    apply_conjAut, mul_inv_eq_iff_eq_mul, mem_centralizerSubgroup, eq_comm]

/-- Commuting a `G`-element past `γ ∈ nonnegSubmonoid deg` conjugates it by `conjAut`. -/
theorem mul_toNonnegSubmonoid (γ : nonnegSubmonoid deg) (g : G) :
    γ * toNonnegSubmonoid ι deg hker g =
      toNonnegSubmonoid ι deg hker (conjAut ι deg hι hker γ.val g) * γ := by
  ext; simp [mul_assoc]
end ConjAut

/-- Elements of `centralizerSubgroup ι γ.val` commute with `γ` inside `nonnegSubmonoid deg`. -/
theorem commute_toNonnegSubmonoid_comp_subtype (hker : ι.range = deg.ker)
    (γ : nonnegSubmonoid deg) (z : centralizerSubgroup ι γ.val) :
    Commute ((toNonnegSubmonoid ι deg hker).comp (centralizerSubgroup ι γ.val).subtype z) γ :=
  Subtype.ext <| by simpa using mem_centralizerSubgroup.1 z.property

/-- Conjugation of `γ : nonnegSubmonoid deg` by `k : G` preserves `nonnegSubmonoid deg`. -/
def conjNonneg (k : G) (γ : nonnegSubmonoid deg) : nonnegSubmonoid deg :=
  ⟨ι k * γ.val * (ι k)⁻¹, by
    rw [mem_nonnegSubmonoid, deg.map_mul, deg.map_mul, deg.map_inv, mul_inv_cancel_comm]
    exact γ.property⟩

@[simp] theorem coe_conjNonneg (k : G) (γ : nonnegSubmonoid deg) :
    (conjNonneg ι deg k γ : Γtilde) = ι k * γ.val * (ι k)⁻¹ := by rfl

/-- Conjugating `γ` by `k : G` inside `nonnegSubmonoid deg` satisfies `(k γ k⁻¹) * k = k * γ`. -/
theorem conjNonneg_mul_toNonnegSubmonoid (hker : ι.range = deg.ker) (k : G)
    (γ : nonnegSubmonoid deg) :
    conjNonneg ι deg k γ * toNonnegSubmonoid ι deg hker k =
      toNonnegSubmonoid ι deg hker k * γ := by ext; simp [mul_assoc]

/-- Conjugation by `k : G` identifies `Z_γ` with `Z_{k γ k⁻¹}`. -/
def conjCentralizerEquiv (k : G) (γ : nonnegSubmonoid deg) :
    centralizerSubgroup ι γ.val ≃* centralizerSubgroup ι (conjNonneg ι deg k γ).val :=
  TauCeti.Subgroup.congrOfMapEq (MulAut.conj k) <| by
    ext x; simp only [Subgroup.mem_map, mem_centralizerSubgroup, coe_conjNonneg]
    refine ⟨?_, fun hx ↦ ⟨k⁻¹ * x * k, ?_, by simp [MulAut.conj_apply, mul_assoc]⟩⟩
    · rintro ⟨z, hz, rfl⟩
      simpa [MulAut.conj_apply, map_mul, map_inv, mul_assoc] using
        congrArg (fun y ↦ ι k * y * (ι k)⁻¹) hz
    · simpa [map_mul, map_inv, mul_assoc] using congrArg (fun y ↦ (ι k)⁻¹ * y * ι k) hx

@[simp] theorem coe_conjCentralizerEquiv_apply (k : G) (γ : nonnegSubmonoid deg)
    (z : centralizerSubgroup ι γ.val) :
    (conjCentralizerEquiv ι deg k γ z : G) = k * z.val * k⁻¹ := by
  simp [conjCentralizerEquiv, TauCeti.Subgroup.coe_congrOfMapEq_apply]
@[simp] theorem coe_conjCentralizerEquiv_symm_apply (k : G) (γ : nonnegSubmonoid deg)
    (z : centralizerSubgroup ι (conjNonneg ι deg k γ).val) :
    ((conjCentralizerEquiv ι deg k γ).symm z : G) = k⁻¹ * z.val * k := by
  simp [conjCentralizerEquiv, TauCeti.Subgroup.coe_congrOfMapEq_symm_apply]
end ExtensionMaps

/-- The fiber `{ γ ∈ Γ | deg γ = ofAdd d }` of elements of degree `d : ℕ` in
`nonnegSubmonoid deg`. -/
@[ext]
structure DegreeFiber {Γtilde : Type*} [Monoid Γtilde]
    (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) where
  /-- Underlying element of `nonnegSubmonoid deg`. -/
  val : nonnegSubmonoid deg
  /-- Degree condition `deg val.val = Multiplicative.ofAdd d`. -/
  deg_eq : deg val.val = Multiplicative.ofAdd (d : ℤ)

namespace DegreeFiber

/-- Conjugation action of `ConjAct Γtilde` on `DegreeFiber deg d`. -/
instance instMulActionConjAct (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) :
    MulAction (ConjAct Γtilde) (DegreeFiber deg d) where
  smul g γ :=
    ⟨⟨g • γ.val.val, by
        rw [mem_nonnegSubmonoid, ConjAct.smul_def, deg.map_mul, deg.map_mul, deg.map_inv,
          mul_inv_cancel_comm]; exact γ.val.property⟩,
      by simp only [ConjAct.smul_def, deg.map_mul, deg.map_inv, mul_inv_cancel_comm, γ.deg_eq]⟩
  one_smul γ := DegreeFiber.ext <| Subtype.ext <| one_smul (ConjAct Γtilde) γ.val.val
  mul_smul g₁ g₂ γ := DegreeFiber.ext <| Subtype.ext <| mul_smul g₁ g₂ γ.val.val

/-- Conjugation action of `G` on `DegreeFiber deg d` induced by `ι : G →* Γtilde`. -/
@[instance_reducible]
def conjAction (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) :
    MulAction G (DegreeFiber deg d) :=
  MulAction.compHom (DegreeFiber deg d) (ConjAct.toConjAct.toMonoidHom.comp ι)

variable {deg : Γtilde →* Multiplicative ℤ} {d : ℕ}

@[simp] theorem conjAct_smul_val (g : ConjAct Γtilde) (γ : DegreeFiber deg d) :
    (g • γ).val.val = g • γ.val.val := by rfl

/-- Conjugation of an element of `DegreeFiber deg d` by `k : G`. -/
def conj (ι : G →* Γtilde) (k : G) (γ : DegreeFiber deg d) : DegreeFiber deg d :=
  let _ := conjAction ι deg d; k • γ

@[simp] theorem val_conj (ι : G →* Γtilde) (k : G) (γ : DegreeFiber deg d) :
    (conj ι k γ).val = conjNonneg ι deg k γ.val := by ext; exact ConjAct.smul_def _ _

/-- Each degree fiber `DegreeFiber deg d` is finite when the kernel group `G` is finite. -/
theorem finite [Finite G] (ι : G →* Γtilde) (hker : ι.range = deg.ker) (d : ℕ) :
    Finite (DegreeFiber deg d) := by
  have : Finite deg.ker := hker ▸ Finite.of_surjective ι.rangeRestrict ι.rangeRestrict_surjective
  have := deg.finite_fiber (Multiplicative.ofAdd (d : ℤ))
  exact .of_injective (fun x : DegreeFiber deg d ↦ (⟨x.val.val, x.deg_eq⟩ : { γ // deg γ = _ }))
    fun _ _ h ↦ DegreeFiber.ext <| Subtype.ext <| Subtype.mk.inj h

end DegreeFiber

section ConjClasses
variable (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (d : ℕ)

/-- Equivalence relation of `G`-conjugacy on `DegreeFiber deg d`. -/
def conjSetoid : Setoid (DegreeFiber deg d) :=
  let _ := DegreeFiber.conjAction ι deg d; MulAction.orbitRel G (DegreeFiber deg d)

/-- `G`-conjugacy classes of degree-`d` elements in `nonnegSubmonoid deg`. -/
abbrev ConjClasses : Type _ := Quotient (conjSetoid ι deg d)

@[simp] theorem conjSetoid_rel (γ₁ γ₂ : DegreeFiber deg d) :
    (conjSetoid ι deg d) γ₁ γ₂ ↔ ∃ k : G, γ₁.val.val = ι k * γ₂.val.val * (ι k)⁻¹ := by
  let _ := DegreeFiber.conjAction ι deg d
  rw [conjSetoid, MulAction.orbitRel_apply, MulAction.mem_orbit_iff]
  refine ⟨fun ⟨k, hk⟩ ↦ ⟨k, hk ▸ congrArg Subtype.val (DegreeFiber.val_conj ι k γ₂)⟩,
    fun ⟨k, hk⟩ ↦ ⟨k, DegreeFiber.ext <| Subtype.ext <|
      (congrArg Subtype.val (DegreeFiber.val_conj ι k γ₂)).trans hk.symm⟩⟩

theorem conjClasses_mk_eq_iff {γ₁ γ₂ : DegreeFiber deg d} :
    (Quotient.mk (conjSetoid ι deg d) γ₁ : ConjClasses ι deg d) =
        Quotient.mk (conjSetoid ι deg d) γ₂ ↔
      ∃ k : G, γ₁.val.val = ι k * γ₂.val.val * (ι k)⁻¹ := by rw [Quotient.eq, conjSetoid_rel]

@[simp] theorem mk_conj (k : G) (γ : DegreeFiber deg d) :
    (Quotient.mk (conjSetoid ι deg d) (DegreeFiber.conj ι k γ) : ConjClasses ι deg d) =
      Quotient.mk (conjSetoid ι deg d) γ := (conjClasses_mk_eq_iff ι deg d).2 ⟨k, by simp⟩

/-- The stabilizer of `γ` under `DegreeFiber.conjAction` is `centralizerSubgroup ι γ.val.val`. -/
theorem stabilizer_conjAction_eq (γ : DegreeFiber deg d) :
    let _ := DegreeFiber.conjAction ι deg d
    MulAction.stabilizer G γ = centralizerSubgroup ι γ.val.val := by
  let _ := DegreeFiber.conjAction ι deg d; ext g
  have hval : (g • γ).val.val = ι g * γ.val.val * (ι g)⁻¹ :=
    congrArg Subtype.val (DegreeFiber.val_conj ι g γ)
  rw [MulAction.mem_stabilizer_iff, mem_centralizerSubgroup, DegreeFiber.ext_iff, Subtype.ext_iff,
    hval, mul_inv_eq_iff_eq_mul]
end ConjClasses

/-- The quotient `ConjClasses ι deg d` is finite when the kernel group `G` is finite. -/
theorem ConjClasses.finite [Finite G] (ι : G →* Γtilde) {deg : Γtilde →* Multiplicative ℤ}
    (hker : ι.range = deg.ker) (d : ℕ) : Finite (ConjClasses ι deg d) := by
  have := DegreeFiber.finite ι hker d; infer_instance

section OrbitBijection
variable {ι : G →* Γtilde} {deg : Γtilde →* Multiplicative ℤ}

section Basepoint
variable (hι : Function.Injective ι) (hker : ι.range = deg.ker) {d : ℕ}

/-- Given a basepoint `γ₀ : DegreeFiber deg d`, `DegreeFiber deg d` identifies with `G` via the
unique `g : G` satisfying `ι g * γ.val.val = γ₀.val.val`. -/
def degreeFiberEquivGroup (γ₀ : DegreeFiber deg d) : DegreeFiber deg d ≃ G :=
  let hmem (γ : DegreeFiber deg d) : γ₀.val.val / γ.val.val ∈ ι.range :=
    hker.symm ▸ deg.div_mem_ker_iff.2 (γ₀.deg_eq.trans γ.deg_eq.symm)
  let inv (g : G) : DegreeFiber deg d := ⟨toNonnegSubmonoid ι deg hker g⁻¹ * γ₀.val, by
    simpa [MonoidHom.mem_ker.1 (hker ▸ MonoidHom.mem_range.2 ⟨g, rfl⟩)] using γ₀.deg_eq⟩
  { toFun := fun γ ↦ (MonoidHom.mem_range.1 (hmem γ)).choose
    invFun := inv
    left_inv := fun γ ↦ DegreeFiber.ext <| Subtype.ext <| by
      have h := (MonoidHom.mem_range.1 (hmem γ)).choose_spec
      simp only [inv, Submonoid.coe_mul, coe_toNonnegSubmonoid, map_inv]
      rw [h, div_eq_mul_inv]; group
    right_inv := fun g ↦ hι <| by
      have h := (MonoidHom.mem_range.1 (hmem (inv g))).choose_spec
      simp only [inv, Submonoid.coe_mul, coe_toNonnegSubmonoid, map_inv, div_eq_mul_inv] at h ⊢
      rw [h]; group }

/-- Characteristic relation of `degreeFiberEquivGroup`: `ι (e γ) * γ = γ₀`. -/
theorem apply_degreeFiberEquivGroup_mul (γ₀ γ : DegreeFiber deg d) :
    ι (degreeFiberEquivGroup hι hker γ₀ γ) * γ.val.val = γ₀.val.val := by
  have h := (MonoidHom.mem_range.1 (hker.symm ▸ deg.div_mem_ker_iff.2
    (γ₀.deg_eq.trans γ.deg_eq.symm))).choose_spec
  dsimp only [degreeFiberEquivGroup]; rw [Equiv.coe_fn_mk, h, div_mul_cancel]

@[simp] theorem degreeFiberEquivGroup_symm_val (γ₀ : DegreeFiber deg d) (g : G) :
    ((degreeFiberEquivGroup hι hker γ₀).symm g).val =
      toNonnegSubmonoid ι deg hker g⁻¹ * γ₀.val := by rfl
@[simp] theorem degreeFiberEquivGroup_self (γ₀ : DegreeFiber deg d) :
    degreeFiberEquivGroup hι hker γ₀ γ₀ = 1 :=
  hι (by simpa using apply_degreeFiberEquivGroup_mul hι hker γ₀ γ₀)

/-- How `degreeFiberEquivGroup` transforms under `G`-conjugation on `DegreeFiber deg d`. -/
theorem degreeFiberEquivGroup_conj {hker : ι.range = deg.ker} (γ₀ γ : DegreeFiber deg d) (g : G) :
    degreeFiberEquivGroup hι hker γ₀ (DegreeFiber.conj ι g γ) =
      degreeFiberEquivGroup hι hker γ₀ γ * conjAut ι deg hι hker γ.val.val g * g⁻¹ := by
  apply hι; apply mul_right_cancel (b := (DegreeFiber.conj ι g γ).val.val)
  rw [apply_degreeFiberEquivGroup_mul, ← apply_degreeFiberEquivGroup_mul hι hker γ₀ γ]
  simp only [DegreeFiber.val_conj, coe_conjNonneg, map_mul, map_inv, apply_conjAut]; group
end Basepoint

/-- Orbit-stabilizer decomposition of `DegreeFiber deg d` into `G`-conjugacy classes and
centralizer cosets. -/
def orbitStabilizerEquiv (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ) (d : ℕ) :
    DegreeFiber deg d ≃
      (c : ConjClasses ι deg d) × G ⧸ centralizerSubgroup ι c.out.val.val :=
  letI := DegreeFiber.conjAction ι deg d
  (MulAction.selfEquivSigmaOrbitsQuotientStabilizer G (DegreeFiber deg d)).trans <|
    Equiv.sigmaCongrRight fun c : MulAction.orbitRel.Quotient G (DegreeFiber deg d) ↦
      Subgroup.quotientEquivOfEq (stabilizer_conjAction_eq ι deg d c.out)

@[simp] theorem orbitStabilizerEquiv_symm_mk (ι : G →* Γtilde)
    (deg : Γtilde →* Multiplicative ℤ) {d : ℕ} (c : ConjClasses ι deg d) (g : G) :
    (orbitStabilizerEquiv ι deg d).symm ⟨c, QuotientGroup.mk g⟩ = DegreeFiber.conj ι g c.out := by
  let _ := DegreeFiber.conjAction ι deg d
  -- `ConjClasses` is `Quotient (conjSetoid ...)`, definitionally `MulAction.orbitRel.Quotient`.
  let c' : MulAction.orbitRel.Quotient G (DegreeFiber deg d) := c
  have hqeq : (Subgroup.quotientEquivOfEq (stabilizer_conjAction_eq ι deg d c'.out)).symm
      (QuotientGroup.mk g) = QuotientGroup.mk g :=
    (Subgroup.quotientEquivOfEq _).symm_apply_eq.2 (Subgroup.quotientEquivOfEq_mk _ g).symm
  dsimp only [orbitStabilizerEquiv]
  erw [Equiv.symm_trans_apply, Equiv.sigmaCongrRight_symm, Equiv.sigmaCongrRight_apply, hqeq]
  exact MulAction.selfEquivSigmaOrbitsQuotientStabilizer_symm_mk c' g

@[simp] theorem fst_orbitStabilizerEquiv (ι : G →* Γtilde) (deg : Γtilde →* Multiplicative ℤ)
    {d : ℕ} (γ : DegreeFiber deg d) :
    (orbitStabilizerEquiv ι deg d γ).fst = Quotient.mk (conjSetoid ι deg d) γ := by
  obtain ⟨g, hg⟩ := QuotientGroup.mk_surjective (orbitStabilizerEquiv ι deg d γ).snd
  have hγ : DegreeFiber.conj ι g (orbitStabilizerEquiv ι deg d γ).fst.out = γ := by
    rw [← orbitStabilizerEquiv_symm_mk, hg, Sigma.eta, Equiv.symm_apply_apply]
  conv_rhs => rw [← hγ, mk_conj, Quotient.out_eq]

end OrbitBijection
end TauCeti.MonoidExtension
end
