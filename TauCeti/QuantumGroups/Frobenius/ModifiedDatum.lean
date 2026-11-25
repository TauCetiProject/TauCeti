/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Data.ZMod.Basic
public import Mathlib.GroupTheory.Index
public import TauCeti.LinearAlgebra.Matrix.Cartan.Datum.Symmetrizable
public import TauCeti.QuantumGroups.Frobenius.OrderData

import Mathlib.LinearAlgebra.FreeModule.PID

/-!
# Lusztig's modified Cartan datum on weight and coweight lattices

Given a symmetrizable `TauCeti.CartanDatum` `D` on full weight and coweight lattices `X` and `Y` and
a parameter order `L ≥ 1`, Lusztig's root-of-unity quantum Frobenius homomorphism lands in the
algebra attached to a **modified Cartan datum** `D*` on modified lattices `(X*, Y*)`:

* the **modified weight lattice** `X* ⊆ X` (`TauCeti.CartanDatum.modifiedWeightLattice`) consists of
  those weights `λ ∈ X` with `ℓᵢ ∣ ⟨λ, hᵢ⟩` for every simple coroot `hᵢ`, realized as the kernel of
  the residue map `X →ₗ[ℤ] ∏ᵢ ℤ/ℓᵢℤ` (`TauCeti.CartanDatum.weightResidue`);
* when the index type is finite and `L > 0`, `X*` has finite index in `X`
  (`TauCeti.CartanDatum.finiteIndex_modifiedWeightLattice`), and whenever `X` is finitely generated
  over `ℤ`, `X*` is automatically free of finite rank and hence reflexive
  (`TauCeti.CartanDatum.isReflexive_modifiedWeightLattice`); for `L ≠ 0`, `X*` is reflexive with no
  finiteness assumption, since `X` is reflexive and `X*` contains `L • X`
  (`TauCeti.CartanDatum.isReflexive_modifiedWeightLattice_of_neZero`);
* the **modified simple roots** are `αᵢ* = ℓᵢ • αᵢ ∈ X*` (`TauCeti.CartanDatum.modifiedRoot`), and
  `X*` is stable under every simple reflection `sᵢ`
  (`TauCeti.CartanDatum.reflection_mem_modifiedWeightLattice`);
* the **modified coweight lattice** is the dual `Y* = Hom(X*, ℤ)`, into which `Y` embeds via
  restriction of the pairing (`TauCeti.CartanDatum.coweightToModified`), and the **modified simple
  coroots** are `hᵢ*(λ) = ⟨λ, hᵢ⟩ / ℓᵢ` (`TauCeti.CartanDatum.modifiedCoroot`), satisfying
  `ℓᵢ • hᵢ* = hᵢ|_{X*}` and `⟨αⱼ*, hᵢ*⟩ = (ℓⱼ aᵢⱼ) / ℓᵢ = aᵢⱼ*`;
* for `L > 0` (so that `X*` is reflexive over `ℤ`), these data assemble into
  `TauCeti.CartanDatum.modifiedDatum`, whose underlying `SymmetrizableDatum` is
  `D.toSymmetrizableDatum.modifiedDatum` and whose simple reflections agree with the restrictions of
  `D.reflection` to `X*`; restriction `Y → Y*` intertwines the simple coreflections
  (`TauCeti.CartanDatum.coweightToModified_coreflection`), and `D*` has the Cartan products
  `aᵢⱼ aⱼᵢ`, hence the braid lengths, of `D`
  (`TauCeti.SymmetrizableDatum.coxeterMatrixOfGeneralizedCartanMatrix_modifiedDatum_cartan`).

Normalizing the symmetrizer `d` to `d_norm = d / gcdᵢ dᵢ` and replacing `L` by the reduced order
`L' = L / gcd(L, gcdᵢ dᵢ)` leaves the Frobenius orders `ℓᵢ` and the modified weight lattice `X*`
unchanged (`TauCeti.CartanDatum.frobeniusOrder_normalizeSymmetrizer`,
`TauCeti.CartanDatum.modifiedWeightLattice_normalizeSymmetrizer`).

## References

* G. Lusztig, *Introduction to Quantum Groups*, Progress in Mathematics 110, Birkhäuser, 1993,
  §2.2.4, §35.1.
* K. McGerty, *Generalized `q`-Schur algebras and quantum Frobenius*, Adv. Math. 214 (2007),
  116–131 (arXiv:math/0601511), §4.
-/

public section

namespace TauCeti

namespace CartanDatum

open Module

variable {ι X Y : Type*} [AddCommGroup X] [AddCommGroup Y] (D : CartanDatum ι X Y)

/-! ### Order data lifted from the underlying `SymmetrizableDatum` -/

/-- The Frobenius order `ℓᵢ = L / gcd(L, dᵢ)` of a `CartanDatum` at node `i`. -/
def frobeniusOrder (L : ℕ) (i : ι) : ℕ :=
  D.toSymmetrizableDatum.frobeniusOrder L i

@[simp]
lemma toSymmetrizableDatum_frobeniusOrder (L : ℕ) (i : ι) :
    D.toSymmetrizableDatum.frobeniusOrder L i = D.frobeniusOrder L i := (rfl)

lemma frobeniusOrder_def (L : ℕ) (i : ι) :
    D.frobeniusOrder L i = L / Nat.gcd L (D.symmetrizer i) := by
  simpa using D.toSymmetrizableDatum.frobeniusOrder_def L i

lemma frobeniusOrder_pos {L : ℕ} (hL : 0 < L) (i : ι) : 0 < D.frobeniusOrder L i :=
  D.toSymmetrizableDatum.frobeniusOrder_pos hL i

lemma frobeniusOrder_ne_zero {L : ℕ} (hL : 0 < L) (i : ι) : D.frobeniusOrder L i ≠ 0 :=
  D.toSymmetrizableDatum.frobeniusOrder_ne_zero hL i

lemma frobeniusOrder_dvd (L : ℕ) (i : ι) : D.frobeniusOrder L i ∣ L :=
  D.toSymmetrizableDatum.frobeniusOrder_dvd L i

/-- The target root-of-unity parameter `ζᵢ* = ζ^(dᵢ ℓᵢ²)` of a `CartanDatum` at node `i`. -/
def frobeniusTarget {M : Type*} [Monoid M] (ζ : M) (L : ℕ) (i : ι) : M :=
  D.toSymmetrizableDatum.frobeniusTarget ζ L i

@[simp]
lemma toSymmetrizableDatum_frobeniusTarget {M : Type*} [Monoid M] (ζ : M) (L : ℕ) (i : ι) :
    D.toSymmetrizableDatum.frobeniusTarget ζ L i = D.frobeniusTarget ζ L i := (rfl)

lemma frobeniusTarget_def {M : Type*} [Monoid M] (ζ : M) (L : ℕ) (i : ι) :
    D.frobeniusTarget ζ L i = ζ ^ (D.symmetrizer i * D.frobeniusOrder L i ^ 2) := by
  simpa using D.toSymmetrizableDatum.frobeniusTarget_def ζ L i

/-- If `ζ^(2 L) = 1`, then `(ζᵢ*)² = 1` at every node `i`. -/
theorem frobeniusTarget_sq_eq_one {M : Type*} [Monoid M] {ζ : M} {L : ℕ}
    (hζ : ζ ^ (2 * L) = 1) (i : ι) :
    D.frobeniusTarget ζ L i ^ 2 = 1 :=
  D.toSymmetrizableDatum.frobeniusTarget_sq_eq_one hζ i

/-- Parameter order `L` is **nondivisible** for `D` if `L` is coprime to every `dᵢ`. -/
def Nondivisible (L : ℕ) : Prop :=
  D.toSymmetrizableDatum.Nondivisible L

@[simp]
lemma toSymmetrizableDatum_nondivisible (L : ℕ) :
    D.toSymmetrizableDatum.Nondivisible L ↔ D.Nondivisible L := .rfl

lemma nondivisible_def (L : ℕ) :
    D.Nondivisible L ↔ ∀ i, Nat.Coprime L (D.symmetrizer i) := by
  simpa using D.toSymmetrizableDatum.nondivisible_def L

theorem Nondivisible.frobeniusOrder_eq {D : CartanDatum ι X Y} {L : ℕ}
    (h : D.Nondivisible L) (i : ι) :
    D.frobeniusOrder L i = L :=
  SymmetrizableDatum.Nondivisible.frobeniusOrder_eq h i

theorem nondivisible_iff_forall_frobeniusOrder_eq {L : ℕ} (hL : 0 < L) :
    D.Nondivisible L ↔ ∀ i, D.frobeniusOrder L i = L :=
  D.toSymmetrizableDatum.nondivisible_iff_forall_frobeniusOrder_eq hL

/-- **Lusztig's root-of-unity conditions** on `D` at parameter order `L`: the diagram of `D` is
bipartite and `1 - aᵢⱼ ≤ ℓᵢ` whenever `i ≠ j` and `2 ≤ ℓⱼ`. -/
def LusztigConditions (L : ℕ) : Prop :=
  D.toSymmetrizableDatum.LusztigConditions L

@[simp]
lemma toSymmetrizableDatum_lusztigConditions (L : ℕ) :
    D.toSymmetrizableDatum.LusztigConditions L ↔ D.LusztigConditions L := .rfl

lemma lusztigConditions_def (L : ℕ) :
    D.LusztigConditions L ↔
      (diagramGraph D.cartan).IsBipartite ∧
        ∀ i j, i ≠ j → 2 ≤ D.frobeniusOrder L j → 1 - D.cartan i j ≤ D.frobeniusOrder L i := by
  simpa using D.toSymmetrizableDatum.lusztigConditions_def L

theorem LusztigConditions.isBipartite {D : CartanDatum ι X Y} {L : ℕ}
    (h : D.LusztigConditions L) :
    (diagramGraph D.cartan).IsBipartite :=
  ((D.lusztigConditions_def L).mp h).1

theorem LusztigConditions.one_sub_cartan_le {D : CartanDatum ι X Y} {L : ℕ}
    (h : D.LusztigConditions L) {i j : ι}
    (hij : i ≠ j) (hj : 2 ≤ D.frobeniusOrder L j) :
    1 - D.cartan i j ≤ D.frobeniusOrder L i :=
  ((D.lusztigConditions_def L).mp h).2 i j hij hj

/-- The reduced parameter order `L' = L / gcd(L, gcdᵢ dᵢ)` on a finite index type. -/
def reducedOrder [Fintype ι] (L : ℕ) : ℕ :=
  D.toSymmetrizableDatum.reducedOrder L

@[simp]
lemma toSymmetrizableDatum_reducedOrder [Fintype ι] (L : ℕ) :
    D.toSymmetrizableDatum.reducedOrder L = D.reducedOrder L := (rfl)

lemma reducedOrder_def [Fintype ι] (L : ℕ) :
    D.reducedOrder L = L / Nat.gcd L (Finset.univ.gcd D.symmetrizer) := by
  simpa using D.toSymmetrizableDatum.reducedOrder_def L

lemma reducedOrder_pos [Fintype ι] {L : ℕ} (hL : 0 < L) : 0 < D.reducedOrder L :=
  D.toSymmetrizableDatum.reducedOrder_pos hL

lemma reducedOrder_dvd [Fintype ι] (L : ℕ) : D.reducedOrder L ∣ L :=
  D.toSymmetrizableDatum.reducedOrder_dvd L

/-! ### The residue map and the modified weight lattice `X*` -/

/-- The `ℤ`-linear residue map `λ ↦ (⟨λ, hᵢ⟩ mod ℓᵢ)ᵢ` from `X` to `∏ᵢ ℤ/ℓᵢℤ`, whose kernel is the
modified weight lattice `X*`. -/
def weightResidue (L : ℕ) : X →ₗ[ℤ] ∀ i, ZMod (D.frobeniusOrder L i) :=
  LinearMap.pi fun i ↦
    (Int.castAddHom (ZMod (D.frobeniusOrder L i))).toIntLinearMap ∘ₗ D.pairing.flip (D.coroot i)

@[simp]
lemma weightResidue_apply (L : ℕ) (x : X) (i : ι) :
    D.weightResidue L x i = (D.pairing x (D.coroot i) : ZMod (D.frobeniusOrder L i)) := (rfl)

/-- **Lusztig's modified weight lattice** `X* = {λ ∈ X | ∀ i, ℓᵢ ∣ ⟨λ, hᵢ⟩}`, defined as the kernel
of `TauCeti.CartanDatum.weightResidue`. -/
def modifiedWeightLattice (L : ℕ) : Submodule ℤ X :=
  LinearMap.ker (D.weightResidue L)

@[simp]
theorem mem_modifiedWeightLattice_iff (L : ℕ) (x : X) :
    x ∈ D.modifiedWeightLattice L ↔ ∀ i, (D.frobeniusOrder L i : ℤ) ∣ D.pairing x (D.coroot i) := by
  rw [modifiedWeightLattice, LinearMap.mem_ker, funext_iff]
  exact forall_congr' fun i ↦ by
    rw [weightResidue_apply, Pi.zero_apply, ZMod.intCast_zmod_eq_zero_iff_dvd]

@[simp]
theorem modifiedWeightLattice_one : D.modifiedWeightLattice 1 = ⊤ := by
  ext x
  simp [frobeniusOrder_def]

/-- Every `L`-multiple of a weight lies in `X*`, since `ℓᵢ ∣ L`. -/
theorem nsmul_mem_modifiedWeightLattice (L : ℕ) (x : X) :
    L • x ∈ D.modifiedWeightLattice L := by
  rw [mem_modifiedWeightLattice_iff]
  intro i
  rw [map_nsmul, LinearMap.smul_apply, nsmul_eq_mul]
  exact dvd_mul_of_dvd_left (Int.ofNat_dvd.mpr (D.frobeniusOrder_dvd L i)) _

/-- In the nondivisible case, `X*` consists of the weights whose coroot pairings are all multiples
of `L`. -/
theorem Nondivisible.mem_modifiedWeightLattice_iff {D : CartanDatum ι X Y} {L : ℕ}
    (h : D.Nondivisible L) (x : X) :
    x ∈ D.modifiedWeightLattice L ↔ ∀ i, (L : ℤ) ∣ D.pairing x (D.coroot i) := by
  rw [CartanDatum.mem_modifiedWeightLattice_iff]
  exact forall_congr' fun i ↦ by rw [h.frobeniusOrder_eq i]

/-- On a finite index type and for `L > 0`, the modified weight lattice `X*` has finite index in
`X`. -/
theorem finiteIndex_modifiedWeightLattice [Finite ι] {L : ℕ} (hL : 0 < L) :
    (D.modifiedWeightLattice L).toAddSubgroup.FiniteIndex := by
  have : ∀ i, NeZero (D.frobeniusOrder L i) := fun i ↦ ⟨D.frobeniusOrder_ne_zero hL i⟩
  have hker : (D.modifiedWeightLattice L).toAddSubgroup = (D.weightResidue L).toAddMonoidHom.ker :=
    AddSubgroup.ext fun x ↦ (D.mem_modifiedWeightLattice_iff L x).trans <| by
      simp [AddMonoidHom.mem_ker, funext_iff, ZMod.intCast_zmod_eq_zero_iff_dvd]
  rw [hker]
  infer_instance

/-- Every scaled simple root `αⱼ* = ℓⱼ • αⱼ` lies in `X*`. -/
theorem frobeniusOrder_nsmul_root_mem_modifiedWeightLattice (L : ℕ) (j : ι) :
    D.frobeniusOrder L j • D.root j ∈ D.modifiedWeightLattice L := by
  rw [mem_modifiedWeightLattice_iff]
  intro i
  rw [map_nsmul, LinearMap.smul_apply, pairing_root_coroot, nsmul_eq_mul]
  simpa using D.toSymmetrizableDatum.frobeniusOrder_dvd_frobeniusOrder_mul_cartan L i j

/-- The modified weight lattice `X*` is invariant under every simple reflection `sᵢ` of `D`. -/
theorem reflection_mem_modifiedWeightLattice {L : ℕ} {x : X}
    (hx : x ∈ D.modifiedWeightLattice L) (i : ι) :
    D.reflection i x ∈ D.modifiedWeightLattice L := by
  rw [mem_modifiedWeightLattice_iff] at hx ⊢
  intro j
  obtain ⟨k, hk⟩ := hx i
  have hdvd : (D.frobeniusOrder L j : ℤ) ∣ D.frobeniusOrder L i * D.cartan j i := by
    simpa using D.toSymmetrizableDatum.frobeniusOrder_dvd_frobeniusOrder_mul_cartan L j i
  rw [reflection_apply, map_sub, map_zsmul, LinearMap.sub_apply, LinearMap.smul_apply,
    pairing_root_coroot, smul_eq_mul, hk, mul_right_comm]
  exact dvd_sub (hx j) (dvd_mul_of_dvd_left hdvd k)

/-! ### Modified simple roots, coweight inclusion and modified simple coroots -/

/-- The **modified simple root** `αᵢ* = ℓᵢ • αᵢ ∈ X*` at node `i`. -/
def modifiedRoot (L : ℕ) (i : ι) : D.modifiedWeightLattice L :=
  ⟨D.frobeniusOrder L i • D.root i, D.frobeniusOrder_nsmul_root_mem_modifiedWeightLattice L i⟩

@[simp]
lemma coe_modifiedRoot (L : ℕ) (i : ι) :
    (D.modifiedRoot L i : X) = D.frobeniusOrder L i • D.root i := (rfl)

/-- For `L > 0`, the modified simple roots `αᵢ* = ℓᵢ • αᵢ` are `ℤ`-linearly independent in `X*`. -/
theorem linearIndependent_modifiedRoot {L : ℕ} (hL : 0 < L) :
    LinearIndependent ℤ (D.modifiedRoot L) := by
  refine LinearIndependent.of_comp (D.modifiedWeightLattice L).subtype ?_
  convert D.linearIndependent_root.smul_of_isRightRegular
    (w := fun i ↦ (D.frobeniusOrder L i : ℤ))
    (fun i ↦ (IsRegular.of_ne_zero (Int.natCast_ne_zero.mpr (D.frobeniusOrder_ne_zero hL i))).right)
  ext i
  simp [coe_modifiedRoot]

/-- The canonical `ℤ`-linear restriction map `Y →ₗ[ℤ] Hom(X*, ℤ)` sending a coweight `y ∈ Y` to
`λ ↦ ⟨λ, y⟩` on `X*`. -/
def coweightToModified (L : ℕ) : Y →ₗ[ℤ] Dual ℤ (D.modifiedWeightLattice L) :=
  LinearMap.lcomp ℤ ℤ (D.modifiedWeightLattice L).subtype ∘ₗ D.pairing.flip

@[simp]
lemma coweightToModified_apply (L : ℕ) (y : Y) (x : D.modifiedWeightLattice L) :
    D.coweightToModified L y x = D.pairing x.val y := (rfl)

/-- Restricting the coweight `⟨-, y⟩` to `X*` is `D.coweightToModified L y`. -/
@[simp]
lemma dualRestrict_pairing_flip (L : ℕ) (y : Y) :
    (D.modifiedWeightLattice L).dualRestrict (D.pairing.flip y) = D.coweightToModified L y := by
  ext
  simp [Submodule.dualRestrict_apply]

/-- For `L > 0`, the coweight restriction map `Y →ₗ[ℤ] Hom(X*, ℤ)` is injective. -/
theorem coweightToModified_injective {L : ℕ} (hL : 0 < L) :
    Function.Injective (D.coweightToModified L) := by
  rw [injective_iff_map_eq_zero]
  intro y hy
  refine D.pairing.flip.toPerfPair.injective ?_
  rw [map_zero]
  ext x
  have hx := LinearMap.congr_fun hy ⟨L • x, D.nsmul_mem_modifiedWeightLattice L x⟩
  simp only [coweightToModified_apply, map_nsmul, LinearMap.smul_apply, nsmul_eq_mul,
    LinearMap.zero_apply, mul_eq_zero, Int.natCast_eq_zero] at hx
  simpa using hx.resolve_left hL.ne'

/-- The **modified simple coroot** `hᵢ* ∈ Y* = Hom(X*, ℤ)` at node `i`, sending `λ ∈ X*` to the
exact quotient `⟨λ, hᵢ⟩ / ℓᵢ`. -/
def modifiedCoroot (L : ℕ) (i : ι) : Dual ℤ (D.modifiedWeightLattice L) where
  toFun x := D.pairing x.val (D.coroot i) / D.frobeniusOrder L i
  map_add' x x' := by
    simp only [Submodule.coe_add, map_add, LinearMap.add_apply]
    exact Int.add_ediv_of_dvd_left ((D.mem_modifiedWeightLattice_iff L x.val).mp x.property i)
  map_smul' r x := by
    simp only [SetLike.val_smul, map_zsmul, LinearMap.smul_apply, zsmul_eq_mul, RingHom.id_apply]
    exact Int.mul_ediv_assoc r ((D.mem_modifiedWeightLattice_iff L x.val).mp x.property i)

@[simp]
lemma modifiedCoroot_apply (L : ℕ) (i : ι) (x : D.modifiedWeightLattice L) :
    D.modifiedCoroot L i x = D.pairing x.val (D.coroot i) / D.frobeniusOrder L i := (rfl)

/-- Scaling the modified simple coroot `hᵢ*` by `ℓᵢ` recovers the restriction of `hᵢ` to `X*`. -/
@[simp]
theorem frobeniusOrder_nsmul_modifiedCoroot (L : ℕ) (i : ι) :
    D.frobeniusOrder L i • D.modifiedCoroot L i = D.coweightToModified L (D.coroot i) := by
  ext x
  rw [LinearMap.smul_apply, modifiedCoroot_apply, coweightToModified_apply, nsmul_eq_mul]
  exact Int.mul_ediv_cancel' ((D.mem_modifiedWeightLattice_iff L x.val).mp x.property i)

/-- The pairing of `αⱼ*` and `hᵢ*` is the modified Cartan entry `aᵢⱼ* = (ℓⱼ aᵢⱼ) / ℓᵢ`. -/
theorem modifiedCoroot_modifiedRoot {L : ℕ} (hL : 0 < L) (i j : ι) :
    D.modifiedCoroot L i (D.modifiedRoot L j) =
      (D.toSymmetrizableDatum.modifiedDatum L hL).cartan i j := by
  simp [modifiedCoroot_apply, coe_modifiedRoot]

/-- For `L > 0`, the modified simple coroots `hᵢ*` are `ℤ`-linearly independent in
`Y* = Hom(X*, ℤ)`. -/
theorem linearIndependent_modifiedCoroot {L : ℕ} (hL : 0 < L) :
    LinearIndependent ℤ (D.modifiedCoroot L) := by
  rw [linearIndependent_iff']
  intro s g hg i hi
  let N : ℕ := ∏ j ∈ s, D.frobeniusOrder L j
  have hN_pos : 0 < N := Finset.prod_pos fun j _ ↦ D.frobeniusOrder_pos hL j
  have hsum : ∑ j ∈ s, (g j * ↑(N / D.frobeniusOrder L j)) • D.coroot j = 0 := by
    refine D.coweightToModified_injective hL ?_
    rw [map_zero, map_sum]
    have hN_hg : (N : ℤ) • ∑ j ∈ s, g j • D.modifiedCoroot L j = 0 := by rw [hg, smul_zero]
    rw [Finset.smul_sum] at hN_hg
    refine Eq.trans ?_ hN_hg
    refine Finset.sum_congr rfl fun j hj ↦ ?_
    have hdvd : D.frobeniusOrder L j ∣ N := Finset.dvd_prod_of_mem _ hj
    have hmul : (N / D.frobeniusOrder L j) * D.frobeniusOrder L j = N := Nat.div_mul_cancel hdvd
    rw [map_smul, ← D.frobeniusOrder_nsmul_modifiedCoroot L j, ← natCast_zsmul, smul_smul,
      smul_smul, mul_assoc, ← Nat.cast_mul, hmul, mul_comm]
  have hzero := linearIndependent_iff'.mp D.linearIndependent_coroot s
    (fun j ↦ g j * ↑(N / D.frobeniusOrder L j)) hsum i hi
  have hdiv_pos : 0 < N / D.frobeniusOrder L i :=
    Nat.div_pos (Nat.le_of_dvd hN_pos (Finset.dvd_prod_of_mem _ hi)) (D.frobeniusOrder_pos hL i)
  exact (mul_eq_zero.mp hzero).resolve_right (Int.natCast_ne_zero.mpr hdiv_pos.ne')

/-! ### Reflexivity and the modified `CartanDatum` -/

/-- Whenever the weight lattice `X` is finitely generated over `ℤ` (covering every finite-rank root
datum, including `CartanDatum.simplyConnected` and `CartanDatum.rankOne`), the modified weight
lattice `X*` is reflexive over `ℤ`. -/
instance isReflexive_modifiedWeightLattice [Module.Finite ℤ X] (L : ℕ) :
    IsReflexive ℤ (D.modifiedWeightLattice L) := by
  have : IsTorsionFree ℤ X :=
    D.pairing.toPerfPair.injective.moduleIsTorsionFree _ D.pairing.toPerfPair.map_smul
  infer_instance

/-- For `L ≠ 0`, the modified weight lattice `X*` is reflexive over `ℤ` with no finiteness
assumption on `X`: the weight lattice `X` is reflexive because its pairing with `Y` is perfect, and
`X*` contains `L • X`. -/
instance isReflexive_modifiedWeightLattice_of_neZero (L : ℕ) [NeZero L] :
    IsReflexive ℤ (D.modifiedWeightLattice L) where
  bijective_dual_eval' := by
    have := IsReflexive.of_isPerfPair D.pairing
    set W := D.modifiedWeightLattice L
    refine ⟨fun x y hxy ↦ Subtype.ext <| (bijective_dual_eval ℤ X).injective <|
      LinearMap.ext fun g ↦ by simpa using congr($hxy (W.dualRestrict g)), fun Φ ↦ ?_⟩
    -- A form `Φ` on `Hom(X*, ℤ)` is represented on `X` by some `x`; this `x` lies in `X*`
    -- because `hᵢ` restricts to `ℓᵢ • hᵢ*`.
    obtain ⟨x, hx⟩ := (bijective_dual_eval ℤ X).surjective (Φ ∘ₗ W.dualRestrict)
    have hmem : x ∈ W := (D.mem_modifiedWeightLattice_iff L x).mpr fun i ↦
      ⟨Φ (D.modifiedCoroot L i), by
        simpa [W, ← frobeniusOrder_nsmul_modifiedCoroot] using
          congr($hx (D.pairing.flip (D.coroot i)))⟩
    refine ⟨⟨x, hmem⟩, LinearMap.ext fun f ↦ ?_⟩
    -- Test `Φ` against `f ∘ φ`, where `φ : X → X*` is `x ↦ L • x`; this identifies `Φ f` with
    -- `f x` after cancelling `L`.
    let φ : X →ₗ[ℤ] W := (L • LinearMap.id).codRestrict W (D.nsmul_mem_modifiedWeightLattice L)
    have hφ (y : X) (hy : y ∈ W) : φ y = L • ⟨y, hy⟩ := Subtype.ext (by simp [φ])
    have hres : W.dualRestrict (f ∘ₗ φ) = L • f := LinearMap.ext fun y ↦ by simp [hφ _ y.property]
    have := congr($hx (f ∘ₗ φ))
    simp only [Dual.eval_apply, LinearMap.comp_apply, hres, hφ _ hmem, map_nsmul,
      nsmul_eq_mul] at this
    exact mul_left_cancel₀ (Nat.cast_ne_zero.mpr (NeZero.ne L)) this

/-- **Lusztig's modified Cartan datum** `D*` on `(X*, Y*) = (X*, Hom(X*, ℤ))` at parameter order
`L > 0`, with simple roots `αᵢ* = ℓᵢ • αᵢ`, simple coroots `hᵢ*(λ) = ⟨λ, hᵢ⟩ / ℓᵢ`, and modified
symmetrizer `dᵢ* = ℓᵢ² dᵢ`. The pairing of `X*` with `Hom(X*, ℤ)` is perfect because `X*` is
reflexive for `L ≠ 0` (`TauCeti.CartanDatum.isReflexive_modifiedWeightLattice_of_neZero`). -/
def modifiedDatum (L : ℕ) (hL : 0 < L) :
    CartanDatum ι (D.modifiedWeightLattice L) (Dual ℤ (D.modifiedWeightLattice L)) where
  pairing := Dual.eval ℤ (D.modifiedWeightLattice L)
  isPerfPair_pairing := by
    have : NeZero L := ⟨hL.ne'⟩
    infer_instance
  root := D.modifiedRoot L
  coroot := D.modifiedCoroot L
  linearIndependent_root := D.linearIndependent_modifiedRoot hL
  linearIndependent_coroot := D.linearIndependent_modifiedCoroot hL
  pairing_root_coroot_self i := by
    rw [Dual.eval_apply, D.modifiedCoroot_modifiedRoot hL]
    exact (D.toSymmetrizableDatum.modifiedDatum L hL).isGeneralizedCartan.diag i
  pairing_root_coroot_nonpos {i j} hij := by
    rw [Dual.eval_apply, D.modifiedCoroot_modifiedRoot hL]
    exact (D.toSymmetrizableDatum.modifiedDatum L hL).isGeneralizedCartan.offDiag_nonpos i j hij
  symmetrizer i := (D.toSymmetrizableDatum.modifiedDatum L hL).symmetrizer i
  symmetrizer_pos i := (D.toSymmetrizableDatum.modifiedDatum L hL).symmetrizer_pos i
  symmetrizer_mul_pairing i j := by
    simp only [Dual.eval_apply, D.modifiedCoroot_modifiedRoot hL]
    exact (D.toSymmetrizableDatum.modifiedDatum L hL).symmetrizes i j

@[simp]
lemma modifiedDatum_pairing (L : ℕ) (hL : 0 < L) :
    (D.modifiedDatum L hL).pairing = Dual.eval ℤ (D.modifiedWeightLattice L) := (rfl)

@[simp]
lemma modifiedDatum_root (L : ℕ) (hL : 0 < L) :
    (D.modifiedDatum L hL).root = D.modifiedRoot L := (rfl)

@[simp]
lemma modifiedDatum_coroot (L : ℕ) (hL : 0 < L) :
    (D.modifiedDatum L hL).coroot = D.modifiedCoroot L := (rfl)

@[simp]
lemma modifiedDatum_symmetrizer (L : ℕ) (hL : 0 < L) (i : ι) :
    (D.modifiedDatum L hL).symmetrizer i = D.frobeniusOrder L i ^ 2 * D.symmetrizer i := by
  simp [modifiedDatum]

@[simp]
theorem cartan_modifiedDatum (L : ℕ) (hL : 0 < L) :
    (D.modifiedDatum L hL).cartan = (D.toSymmetrizableDatum.modifiedDatum L hL).cartan := by
  ext i j
  rw [cartan_apply]
  exact D.modifiedCoroot_modifiedRoot hL i j

@[simp]
theorem toSymmetrizableDatum_modifiedDatum (L : ℕ) (hL : 0 < L) :
    (D.modifiedDatum L hL).toSymmetrizableDatum = D.toSymmetrizableDatum.modifiedDatum L hL := by
  ext <;> simp

/-- Every simple reflection of the modified datum `D*` agrees with the restriction of the
corresponding simple reflection of `D` to `X*`. -/
@[simp]
theorem coe_reflection_modifiedDatum (L : ℕ) (hL : 0 < L) (i : ι) (x : D.modifiedWeightLattice L) :
    ((D.modifiedDatum L hL).reflection i x : X) = D.reflection i x := by
  have hdvd := (D.mem_modifiedWeightLattice_iff L x.val).mp x.property i
  have hmul : D.pairing x.val (D.coroot i) / D.frobeniusOrder L i * D.frobeniusOrder L i =
      D.pairing x.val (D.coroot i) := Int.ediv_mul_cancel hdvd
  rw [reflection_apply, reflection_apply, Submodule.coe_sub, SetLike.val_smul,
    modifiedDatum_pairing, modifiedDatum_coroot, modifiedDatum_root, Dual.eval_apply,
    modifiedCoroot_apply, coe_modifiedRoot, ← natCast_zsmul, smul_smul, hmul]

/-- Restricting coweights to `X*` intertwines the simple coreflections of `D` and of `D*`. -/
theorem coweightToModified_coreflection (L : ℕ) (hL : 0 < L) (i : ι) (y : Y) :
    D.coweightToModified L (D.coreflection i y) =
      (D.modifiedDatum L hL).coreflection i (D.coweightToModified L y) := by
  ext x
  simp [coreflection_apply, ← frobeniusOrder_nsmul_modifiedCoroot, coe_modifiedRoot]
  ring

/-- The toral directions of `D*` are rescaled restrictions of those of `D`:
`ℓᵢ² dᵢ hᵢ* = ℓᵢ (dᵢ hᵢ)|_{X*}`. -/
@[simp]
theorem simpleTorus_modifiedDatum (L : ℕ) (hL : 0 < L) (i : ι) :
    (D.modifiedDatum L hL).simpleTorus i =
      D.frobeniusOrder L i • D.coweightToModified L (D.simpleTorus i) := by
  ext x
  simp [simpleTorus_def, ← frobeniusOrder_nsmul_modifiedCoroot]
  ring

/-! ### Invariance under normalization of the symmetrizer -/

section NormalizeSymmetrizer

variable [Fintype ι]

/-- Normalizing the symmetrizer of `D` and replacing `L` by the reduced order `L'` leaves every
Frobenius order unchanged. -/
@[simp]
theorem frobeniusOrder_normalizeSymmetrizer (L : ℕ) (i : ι) :
    D.normalizeSymmetrizer.frobeniusOrder (D.reducedOrder L) i = D.frobeniusOrder L i := by
  rw [← toSymmetrizableDatum_frobeniusOrder, ← toSymmetrizableDatum_frobeniusOrder,
    ← toSymmetrizableDatum_reducedOrder, toSymmetrizableDatum_normalizeSymmetrizer]
  exact D.toSymmetrizableDatum.frobeniusOrder_normalizeSymmetrizer L i

/-- Normalizing the symmetrizer of `D` and replacing `L` by the reduced order `L'` leaves the
modified weight sublattice `X* ⊆ X` unchanged. -/
@[simp]
theorem modifiedWeightLattice_normalizeSymmetrizer (L : ℕ) :
    D.normalizeSymmetrizer.modifiedWeightLattice (D.reducedOrder L) =
      D.modifiedWeightLattice L := by
  ext x
  simp

end NormalizeSymmetrizer

end CartanDatum

end TauCeti
