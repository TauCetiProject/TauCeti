/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import Mathlib.Algebra.Algebra.Basic
public import Mathlib.Algebra.Category.ModuleCat.Basic
public import Mathlib.Algebra.Homology.HomologicalComplex
public import Mathlib.LinearAlgebra.Finsupp.LSum
public import TauCeti.Algebra.BigOperators.AlternatingSum
public import TauCeti.Algebra.BigOperators.Fin
public import TauCeti.Algebra.Group.Conj
import Mathlib.Tactic.Group
import TauCeti.Data.Fin.Tuple.Basic

/-!
# The K-complex of a module over an algebra with Hurwitz generators

Let `c` be a conjugacy class of a group `G`, let `A` be an algebra over a commutative ring `k`, and
let `r : c → A` satisfy the **Hurwitz relations** `r g * r h = r (g h g⁻¹) * r g`. For an
`A`-module `M`, the K-complex `K(M)` of Ellenberg, Venkatesh and Westerland has in degree `q` the
`k`-module `k[c^q] ⊗ M` of `M`-valued finitely supported functions on `q`-tuples of members of
`c`, here `(Fin q → c) →₀ M`, and differential

`(g₀, …, g_q) ⊗ m ↦ ∑ᵢ (-1)ⁱ (g₀, …, ĝᵢ, …, g_q) ⊗ r(gᵢ^(gᵢ₊₁ ⋯ g_q)) m`,

where `g^h = h⁻¹ g h` and the empty product is `1`. Deleting the `i`-th entry is a face map, and the
Hurwitz relations are exactly what makes these faces satisfy the semisimplicial identities, so the
alternating sum squares to zero (`TauCeti.sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero`).

The motivating case is the ring `R = ⨁ₙ H₀(Hurₙ; k)` of components of Hurwitz spaces, with `r g`
the class of the one-term tuple `(g)`: there the homology of `K(M)` in degrees `0` and `1` controls
the stability of a central element of `R` acting on a graded `R`-module `M`. The construction
needs only the Hurwitz relations, so it is made here for any algebra and any module, without
the internal grading.

## Main declarations

* `TauCeti.KComplex.suffixConj`: the conjugate `gᵢ^(gᵢ₊₁ ⋯ gₙ₋₁)` of an entry of a tuple by the
  product of the later entries.
* `TauCeti.KComplex.IsHurwitzFamily`: the Hurwitz relations for a family `r : c → A`.
* `TauCeti.KComplex.face`: the `i`-th face map `K(M)_(q+1) → K(M)_q`.
* `TauCeti.KComplex.face_comp_face`: the semisimplicial identities, from the Hurwitz relations.
* `TauCeti.KComplex.d`: the differential, the alternating sum of the faces, with its value on a
  basis tuple `TauCeti.KComplex.d_single`, its low-degree cases `TauCeti.KComplex.d_zero_single`
  and `TauCeti.KComplex.d_one_single`, and `TauCeti.KComplex.d_comp_d`.
* `TauCeti.kComplex`: the K-complex, a chain complex of `k`-modules, whose differential is
  `KComplex.d` (`TauCeti.kComplex_d`).
* `TauCeti.kComplex_d_eq_zero`: when every `r g` acts by zero, as on `k` through an augmentation,
  every differential vanishes.
* `TauCeti.kComplexMap`: an `A`-linear map induces a chain map, functorially
  (`TauCeti.kComplexMap_id`, `TauCeti.kComplexMap_comp`).

## References

* J. S. Ellenberg, A. Venkatesh, C. Westerland, *Homological stability for Hurwitz spaces and the
  Cohen–Lenstra conjecture over function fields*, Ann. of Math. 183 (2016), §4.1, (4.1.1).
-/

public section

open CategoryTheory

namespace TauCeti

namespace KComplex

variable {G : Type*} [Group G] {c : ConjClasses G} {n : ℕ}

/-- The conjugate `gᵢ^s = s⁻¹ gᵢ s` of the entry `gᵢ` of a tuple `w = (g₀, …, gₙ₋₁)` of members of
the conjugacy class `c` by the product `s = gᵢ₊₁ ⋯ gₙ₋₁` of the later entries, written with the
partial products `Pⱼ = g₀ ⋯ gⱼ₋₁` as `s = Pᵢ₊₁⁻¹ Pₙ`. It is again a member of `c`. -/
def suffixConj (w : Fin n → c.carrier) (i : Fin n) : c.carrier :=
  let s := (Fin.partialProd (fun j ↦ (w j : G)) i.succ)⁻¹ *
    Fin.partialProd (fun j ↦ (w j : G)) (Fin.last n)
  ⟨s⁻¹ * w i * s, c.conj_inv_mem_carrier (w i).property s⟩

/-- The value of `suffixConj w i` in `G`. -/
theorem coe_suffixConj (w : Fin n → c.carrier) (i : Fin n) :
    (suffixConj w i : G) =
      ((Fin.partialProd (fun j ↦ (w j : G)) i.succ)⁻¹ *
          Fin.partialProd (fun j ↦ (w j : G)) (Fin.last n))⁻¹ * w i *
        ((Fin.partialProd (fun j ↦ (w j : G)) i.succ)⁻¹ *
          Fin.partialProd (fun j ↦ (w j : G)) (Fin.last n)) :=
  (rfl)

/-- The conjugate of the entry at position `i` in terms of partial products only:
`Pₙ⁻¹ Pᵢ₊₁ Pᵢ⁻¹ Pₙ`. -/
private theorem coe_suffixConj_eq_partialProd (w : Fin n → c.carrier) (i : Fin n) :
    (suffixConj w i : G) =
      (Fin.partialProd (fun j ↦ (w j : G)) (Fin.last n))⁻¹ *
        Fin.partialProd (fun j ↦ (w j : G)) i.succ *
        (Fin.partialProd (fun j ↦ (w j : G)) i.castSucc)⁻¹ *
        Fin.partialProd (fun j ↦ (w j : G)) (Fin.last n) := by
  rw [coe_suffixConj, ← Fin.partialProd_right_inv (fun j ↦ (w j : G)) i]
  group

/-- The last entry of a tuple is conjugated by the empty product, so it is unchanged. -/
@[simp]
theorem suffixConj_last (w : Fin (n + 1) → c.carrier) :
    suffixConj w (Fin.last n) = w (Fin.last n) :=
  Subtype.ext <| by simp [coe_suffixConj]

/-- Deleting an entry at or before position `i` leaves the entries after the following one, and
hence the conjugate at that position, unchanged. -/
private theorem suffixConj_removeNth_castSucc (w : Fin (n + 2) → c.carrier) {i j : Fin (n + 1)}
    (hij : i ≤ j) : suffixConj (i.castSucc.removeNth w) j = suffixConj w j.succ := by
  apply Subtype.ext
  have hlast : i.castSucc ≤ Fin.last (n + 1) := Fin.le_last _
  have hsucc : i.castSucc ≤ j.succ := (Fin.castSucc_lt_succ_iff.2 hij).le
  have hcast : i.castSucc ≤ j.castSucc := Fin.castSucc_le_castSucc_iff.2 hij
  rw [coe_suffixConj_eq_partialProd, coe_suffixConj_eq_partialProd, ← Fin.removeNth_comp,
    Fin.partialProd_removeNth_of_ge _ hlast,
    Fin.partialProd_removeNth_of_ge _ hsucc, Fin.partialProd_removeNth_of_ge _ hcast]
  simp only [Fin.succ_last, Fin.succ_castSucc]
  group

/-- Deleting an entry after position `i` conjugates the conjugate at `i` by the conjugate of the
deleted entry. -/
private theorem suffixConj_removeNth_succ (w : Fin (n + 2) → c.carrier) {i j : Fin (n + 1)}
    (hij : i ≤ j) :
    (suffixConj (j.succ.removeNth w) i : G) =
      suffixConj w j.succ * suffixConj w i.castSucc * (suffixConj w j.succ : G)⁻¹ := by
  have hlast : j.succ ≤ Fin.last (n + 1) := Fin.le_last _
  have hsucc : i.succ ≤ j.succ := Fin.succ_le_succ_iff.2 hij
  have hcast : i.castSucc ≤ j.succ := (Fin.castSucc_lt_succ_iff.2 hij).le
  simp only [coe_suffixConj_eq_partialProd]
  rw [← Fin.removeNth_comp, Fin.partialProd_removeNth_of_ge _ hlast,
    Fin.partialProd_removeNth_of_le _ hsucc, Fin.partialProd_removeNth_of_le _ hcast]
  simp only [Fin.succ_last, Fin.succ_castSucc]
  group

variable (k : Type*) {A : Type*} (M : Type*) [CommRing k] [Semiring A] [Algebra k A]
  [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- The `i`-th face map `K(M)_(q+1) → K(M)_q` of the K-complex: it deletes the `i`-th entry `gᵢ`
of a tuple and acts on the coefficient by `r(gᵢ^(gᵢ₊₁ ⋯ g_q))`. -/
noncomputable def face (r : c.carrier → A) {q : ℕ} (i : Fin (q + 1)) :
    ((Fin (q + 1) → c.carrier) →₀ M) →ₗ[k] (Fin q → c.carrier) →₀ M :=
  Finsupp.lsum k fun w ↦
    Finsupp.lsingle (i.removeNth w) ∘ₗ DistribSMul.toLinearMap k M (r (suffixConj w i))

variable {k M}

/-- The family `r : c → A` satisfies the **Hurwitz relations** `r g * r h = r (g h g⁻¹) * r g` for
all `g` and `h` in the conjugacy class `c`. -/
def IsHurwitzFamily (r : c.carrier → A) : Prop :=
  ∀ g h : c.carrier, r g * r h = r ⟨g * h * (g : G)⁻¹, c.conj_mem_carrier h.property g⟩ * r g

/-- Unfolds `IsHurwitzFamily` to the Hurwitz relations. -/
theorem isHurwitzFamily_iff {r : c.carrier → A} :
    IsHurwitzFamily r ↔
      ∀ g h : c.carrier, r g * r h = r ⟨g * h * (g : G)⁻¹, c.conj_mem_carrier h.property g⟩ * r g :=
  Iff.rfl

/-- The face map on a basis tuple. -/
@[simp]
theorem face_single (r : c.carrier → A) {q : ℕ} (i : Fin (q + 1)) (w : Fin (q + 1) → c.carrier)
    (m : M) :
    face k M r i (Finsupp.single w m) =
      Finsupp.single (i.removeNth w) (r (suffixConj w i) • m) := by
  simp [face]

/-- The **semisimplicial identities** of the faces of the K-complex: when `r` satisfies the
Hurwitz relations, `∂ᵢ ∘ ∂ⱼ₊₁ = ∂ⱼ ∘ ∂ᵢ` for `i ≤ j`. -/
theorem face_comp_face {r : c.carrier → A} (hr : IsHurwitzFamily r) {q : ℕ} {i j : Fin (q + 1)}
    (hij : i ≤ j) :
    face k M r i ∘ₗ face k M r j.succ = face k M r j ∘ₗ face k M r i.castSucc := by
  refine Finsupp.lhom_ext fun w m ↦ ?_
  simp only [LinearMap.comp_apply, face_single, smul_smul]
  have hconj : suffixConj (i.castSucc.removeNth w) j = suffixConj w j.succ :=
    suffixConj_removeNth_castSucc w hij
  have hrel := isHurwitzFamily_iff.1 hr (suffixConj w j.succ) (suffixConj w i.castSucc)
  rw [show (⟨_, _⟩ : c.carrier) = suffixConj (j.succ.removeNth w) i from
    Subtype.ext (suffixConj_removeNth_succ w hij).symm] at hrel
  rw [hconj, hrel, Fin.removeNth_removeNth_eq_swap, Fin.succAbove_succ_of_le _ _ hij,
    Fin.predAbove_succ_of_le _ _ hij]

variable (k M) in
/-- The differential `K(M)_(q+1) → K(M)_q` of the K-complex, the alternating sum of the faces:
`(g₀, …, g_q) ⊗ m ↦ ∑ᵢ (-1)ⁱ (g₀, …, ĝᵢ, …, g_q) ⊗ r(gᵢ^(gᵢ₊₁ ⋯ g_q)) m`. -/
noncomputable def d (r : c.carrier → A) (q : ℕ) :
    ((Fin (q + 1) → c.carrier) →₀ M) →ₗ[k] (Fin q → c.carrier) →₀ M :=
  ∑ i : Fin (q + 1), (-1 : ℤ) ^ (i : ℕ) • face k M r i

/-- The differential on a basis tuple. -/
theorem d_single (r : c.carrier → A) {q : ℕ} (w : Fin (q + 1) → c.carrier) (m : M) :
    d k M r q (Finsupp.single w m) =
      ∑ i : Fin (q + 1),
        (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (i.removeNth w) (r (suffixConj w i) • m) := by
  simp [d]

/-- In degree one the differential is the action: `(g) ⊗ m ↦ r g • m`, the target being
`M`-valued functions on the single empty tuple. -/
theorem d_zero_single (r : c.carrier → A) (w : Fin 1 → c.carrier) (m : M) :
    d k M r 0 (Finsupp.single w m) = Finsupp.single Fin.elim0 (r (w 0) • m) := by
  have h0 : suffixConj w 0 = w 0 := by simpa using suffixConj_last (n := 0) w
  rw [d_single, Fin.sum_univ_one, h0, Subsingleton.elim (Fin.removeNth 0 w) Fin.elim0]
  simp

/-- In degree two, `(g, h) ⊗ m ↦ (h) ⊗ r(h⁻¹ g h) m - (g) ⊗ r h m`. -/
theorem d_one_single (r : c.carrier → A) (g h : c.carrier) (m : M) :
    d k M r 1 (Finsupp.single ![g, h] m) =
      Finsupp.single ![h]
          (r ⟨(h : G)⁻¹ * g * h, c.conj_inv_mem_carrier g.property h⟩ • m) -
        Finsupp.single ![g] (r h • m) := by
  have h0 : suffixConj ![g, h] 0 = ⟨(h : G)⁻¹ * g * h, c.conj_inv_mem_carrier g.property h⟩ :=
    Subtype.ext <| by
      -- `Pᵢ₊₁⁻¹ Pₙ` for `i = 0` is `P₁⁻¹ P₂ = h`; `simp` normalizes the `Fin` indices to numerals.
      have hs : (Fin.partialProd (fun j ↦ (![g, h] j : G)) (Fin.castSucc 1))⁻¹ *
          Fin.partialProd (fun j ↦ (![g, h] j : G)) (Fin.succ 1) = h := by
        rw [Fin.partialProd_right_inv, Matrix.cons_val_one, Matrix.cons_val_fin_one]
      simp only [Fin.castSucc_one, Fin.succ_one_eq_two] at hs
      simp [coe_suffixConj, hs]
  have h1 : suffixConj ![g, h] 1 = h := by
    simpa using suffixConj_last (n := 1) ![g, h]
  have hw0 : Fin.removeNth 0 ![g, h] = ![h] := by ext i; fin_cases i; simp [Fin.removeNth_apply]
  have hw1 : Fin.removeNth 1 ![g, h] = ![g] := by ext i; fin_cases i; simp [Fin.removeNth_apply]
  rw [d_single, Fin.sum_univ_two, h0, h1, hw0, hw1]
  simp [sub_eq_add_neg]

/-- The differential squares to zero when `r` satisfies the Hurwitz relations. -/
theorem d_comp_d {r : c.carrier → A} (hr : IsHurwitzFamily r) (q : ℕ) :
    d k M r q ∘ₗ d k M r (q + 1) = 0 := by
  refine LinearMap.ext fun x ↦ ?_
  simp only [LinearMap.comp_apply, d]
  rw [LinearMap.sum_apply _ _ x, map_sum]
  simp only [LinearMap.smul_apply, map_zsmul, LinearMap.sum_apply, LinearMap.zero_apply]
  exact sum_neg_one_pow_smul_sum_neg_one_pow_smul_eq_zero
    (fun i j ↦ face k M r j (face k M r i x))
    fun _ _ hij ↦ LinearMap.congr_fun (face_comp_face hr hij) x

/-- If every `r g` acts by zero on `M`, for instance on `k` through an augmentation `A → k` killing
every `r g`, then the differential vanishes. -/
theorem d_eq_zero {r : c.carrier → A} (h : ∀ (g : c.carrier) (m : M), r g • m = 0) (q : ℕ) :
    d k M r q = 0 :=
  Finsupp.lhom_ext fun w m ↦ by simp [d_single, h]

variable {N : Type*} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]

/-- An `A`-linear map applied to the coefficients commutes with the differential. -/
theorem d_comp_mapRange (r : c.carrier → A) (f : M →ₗ[A] N) (q : ℕ) :
    d k N r q ∘ₗ Finsupp.mapRange.linearMap (f.restrictScalars k) =
      Finsupp.mapRange.linearMap (f.restrictScalars k) ∘ₗ d k M r q :=
  Finsupp.lhom_ext fun w m ↦ by simp [d_single, map_sum, map_zsmul]

end KComplex

open KComplex

universe v

variable (k : Type*) {G : Type*} [Group G] {c : ConjClasses G} {A : Type*} [CommRing k]
  [Semiring A] [Algebra k A] (r : c.carrier → A) (hr : IsHurwitzFamily r)
  (M : Type v) [AddCommGroup M] [Module k M] [Module A M] [IsScalarTower k A M]

/-- The **K-complex** `K(M)` of a module `M` over an algebra `A` with a family `r : c → A`
satisfying the Hurwitz relations: the chain complex of `k`-modules with `(Fin q → c) →₀ M` in degree
`q` and differential `KComplex.d`, the alternating sum of the faces `KComplex.face`,
`(g₀, …, g_q) ⊗ m ↦ ∑ᵢ (-1)ⁱ (g₀, …, ĝᵢ, …, g_q) ⊗ r(gᵢ^(gᵢ₊₁ ⋯ g_q)) m`. -/
-- Exposed so that its terms unfold to the modules `(Fin q → c) →₀ M` on which `KComplex.d` and
-- the induced chain maps are defined.
@[expose] noncomputable def kComplex : ChainComplex (ModuleCat k) ℕ :=
  ChainComplex.of (fun q ↦ ModuleCat.of k ((Fin q → c.carrier) →₀ M))
    (fun q ↦ ModuleCat.ofHom (d k M r q)) fun q ↦ by
      rw [← ModuleCat.ofHom_comp, d_comp_d hr, ModuleCat.ofHom_zero]

@[simp]
theorem kComplex_X (q : ℕ) :
    (kComplex k r hr M).X q = ModuleCat.of k ((Fin q → c.carrier) →₀ M) :=
  rfl

@[simp]
theorem kComplex_d (q : ℕ) :
    (kComplex k r hr M).d (q + 1) q = ModuleCat.ofHom (d k M r q) :=
  ChainComplex.of_d (fun q ↦ ModuleCat.of k ((Fin q → c.carrier) →₀ M))
    (fun q ↦ ModuleCat.ofHom (d k M r q)) q

variable {k r hr M}

/-- If every `r g` acts by zero on `M`, for instance on `k` through an augmentation `A → k` killing
every `r g`, then every differential of the K-complex vanishes. -/
theorem kComplex_d_eq_zero (h : ∀ (g : c.carrier) (m : M), r g • m = 0) (i j : ℕ) :
    (kComplex k r hr M).d i j = 0 := by
  by_cases hij : i = j + 1
  · subst hij
    rw [kComplex_d, d_eq_zero h]
    exact ModuleCat.ofHom_zero
  · exact (kComplex k r hr M).shape _ _ fun h ↦ hij h.symm

variable {N P : Type v} [AddCommGroup N] [Module k N] [Module A N] [IsScalarTower k A N]
  [AddCommGroup P] [Module k P] [Module A P] [IsScalarTower k A P]

/-- An `A`-linear map `f : M → N` induces a chain map `K(M) → K(N)`, applying `f` to the
coefficients. -/
noncomputable def kComplexMap (f : M →ₗ[A] N) : kComplex k r hr M ⟶ kComplex k r hr N :=
  ChainComplex.ofHom (fun _ ↦ ModuleCat.ofHom (Finsupp.mapRange.linearMap (f.restrictScalars k)))
    fun q ↦ by
      rw [kComplex_d, kComplex_d]
      exact congrArg ModuleCat.ofHom (d_comp_mapRange r f q)

@[simp]
theorem kComplexMap_f (f : M →ₗ[A] N) (q : ℕ) :
    (kComplexMap (k := k) (r := r) (hr := hr) f).f q =
      ModuleCat.ofHom (Finsupp.mapRange.linearMap (f.restrictScalars k)) :=
  (rfl)

@[simp]
theorem kComplexMap_id : kComplexMap (k := k) (r := r) (hr := hr) (LinearMap.id : M →ₗ[A] M) =
    𝟙 (kComplex k r hr M) := by
  ext q : 1
  simp [LinearMap.restrictScalars_id, Finsupp.mapRange.linearMap_id, ModuleCat.ofHom_id]

@[reassoc, simp]
theorem kComplexMap_comp (f : M →ₗ[A] N) (g : N →ₗ[A] P) :
    kComplexMap (k := k) (r := r) (hr := hr) (g ∘ₗ f) =
      kComplexMap (k := k) (r := r) (hr := hr) f ≫ kComplexMap g := by
  ext q : 1
  simp [LinearMap.restrictScalars_comp, Finsupp.mapRange.linearMap_comp, ModuleCat.ofHom_comp]

end TauCeti
