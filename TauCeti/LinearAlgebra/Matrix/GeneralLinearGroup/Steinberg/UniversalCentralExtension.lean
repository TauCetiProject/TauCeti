/-
Copyright (c) 2026 The Tau Ceti contributors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The Tau Ceti contributors
-/
module

public import TauCeti.GroupTheory.GroupExtension.UniversalCentralExtension
public import TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Centrality
import TauCeti.GroupTheory.Commutator

/-!
# The Steinberg group as the universal central extension of `E(R)`

For an associative unital ring `R`, the canonical homomorphism
`TauCeti.SteinbergGroup.toStableGL : St(R) →* GL_∞(R)` has image the stable elementary subgroup
`E_∞(R)`, and `TauCeti.LinearAlgebra.Matrix.GeneralLinearGroup.Steinberg.Centrality` proves that
its kernel `ker (toStableGL R)` is central in `St(R)`. This file proves the **universal central
extension** half of the Kervaire–Steinberg theorem:

Given an index type `ι` in which any four indices admit a fifth distinct index (in particular
`|ι| ≥ 5` or `Infinite ι`), a homomorphism `φ : St_ι(R) →* G`, and a homomorphism `q : E →* G`
(with `E` in an arbitrary universe) satisfying `φ.range ≤ q.range` and `q.ker ≤ Z(E)`,
commutators `⁅u, v⁆` in `E` depend only on `q(u)` and `q(v)`. Defining
`ψ(x_{ij}(a)) = ⁅u_{im}(a), u_{mj}(1)⁆` using a chosen auxiliary index `m` and lifts `u` in `E`,
the Hall–Witt commutator-associativity lemma `TauCeti.commutatorElement_assoc_of_commute` shows
independence of `m` and establishes all three Steinberg relations in `E`. Since `St_ι(R)` is
perfect, the resulting lift `ψ : St_ι(R) →* E` satisfying `q ∘ ψ = φ` is unique. In particular,
every central extension out of `St_ι(R)`—including `MonoidHom.id (St_ι(R))` and
`SteinbergGroup.toElementarySubgroup R : St(R) →* E_∞(R)`—is a universal central extension.

## Main definitions

* `TauCeti.IndexedSteinbergGroup.liftCentralExtension`: the canonical lift `St_ι(R) →* E` of
  `φ : St_ι(R) →* G` along any homomorphism `q : E →* G` with `φ.range ≤ q.range` and central
  kernel, whenever any four indices in `ι` admit a fifth distinct index.

## Main results

* `TauCeti.SteinbergGroup.isCentralExtension_toElementarySubgroup`: `toElementarySubgroup R` is a
  central extension.
* `TauCeti.IndexedSteinbergGroup.existsUnique_comp_eq_of_ker_le_center`,
  `TauCeti.IndexedSteinbergGroup.existsUnique_comp_eq_of_five_le_card`,
  `TauCeti.IndexedSteinbergGroup.existsUnique_comp_eq_of_infinite`: existence and uniqueness of
  lifts from `St_ι(R)` into central extensions.
* `TauCeti.IndexedSteinbergGroup.isUniversalCentralExtension_of_isCentralExtension`,
  `TauCeti.IndexedSteinbergGroup.isUniversalCentralExtension_id_of_five_le_card`,
  `TauCeti.IndexedSteinbergGroup.isUniversalCentralExtension_id_of_infinite`: `St_ι(R)` is
  centrally closed when `|ι| ≥ 5` or `Infinite ι`.
* `TauCeti.SteinbergGroup.existsUnique_comp_eq_toStableGL`: existence and uniqueness of lifts from
  `St(R)` along any `q : E →* GL_∞(R)` with `E_∞(R) ≤ q.range` and central kernel.
* `TauCeti.SteinbergGroup.isUniversalCentralExtension_toElementarySubgroup`:
  `toElementarySubgroup R` satisfies `MonoidHom.IsUniversalCentralExtension`.
* `TauCeti.steinberg_universalCentralExtension`: the packaged Kervaire–Steinberg universal central
  extension theorem over `GL_∞(R)`.

## References

* R. Steinberg, *Générateurs, relations et revêtements de groupes algébriques*, in *Colloq.
  Théorie des Groupes Algébriques (Bruxelles, 1962)*, Librairie Universitaire, Louvain;
  Gauthier-Villars, Paris (1962), 113–127.
* M. Kervaire, *Multiplicateurs de Schur et K-théorie*, in *Essays on Topology and Related
  Topics* (Mémoires dédiés à Georges de Rham), Springer (1970), 212–225.
* J. Milnor, *Introduction to Algebraic K-Theory*, Annals of Mathematics Studies 72 (1971), §5,
  Theorems 5.1 and 5.10.
* C. A. Weibel, *The K-book: An Introduction to Algebraic K-Theory*, Graduate Studies in
  Mathematics 145 (2013), Chapter III, §5, Theorem 5.2.1, Lemma 5.3.3, and Theorem 5.5.
-/

public section

noncomputable section

open Matrix Subgroup

open scoped commutatorElement

namespace TauCeti

universe u v

/-! ## Universal central extension property -/

namespace IndexedSteinbergGroup

section Universal

variable {ι R G E : Type*} [Ring R] [Group G] [Group E]

private theorem forall_exists_ne_four_of_five_le_card [Fintype ι] (h : 5 ≤ Fintype.card ι) :
    ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d := by
  classical
  intro a b c d
  have hlt : ({a, b, c, d} : Finset ι).card < (Finset.univ : Finset ι).card := by
    calc
      ({a, b, c, d} : Finset ι).card ≤ 4 := by
        refine (Finset.card_insert_le _ _).trans ?_
        refine Nat.add_le_add_right ((Finset.card_insert_le _ _).trans ?_) 1
        exact Nat.add_le_add_right Finset.card_le_two 1
      _ < (Finset.univ : Finset ι).card := by rw [Finset.card_univ]; omega
  obtain ⟨m, -, hm⟩ := Finset.exists_mem_notMem_of_card_lt_card hlt
  exact ⟨m, by simpa [not_or] using hm⟩

private theorem forall_exists_ne_four_of_infinite [Infinite ι] :
    ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d := by
  classical
  intro a b c d
  obtain ⟨m, hm⟩ := Infinite.exists_notMem_finset ({a, b, c, d} : Finset ι)
  exact ⟨m, by simpa [not_or] using hm⟩

/-- Chosen lift in `E` of `φ (x hij a)` along `q : E →* G` when `φ.range ≤ q.range`. -/
private def chooseLift {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) {i j : ι} (hij : i ≠ j) (a : R) : E :=
  (hq_range ⟨x hij a, rfl⟩).choose

private theorem apply_chooseLift {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) {i j : ι} (hij : i ≠ j) (a : R) :
    q (chooseLift hq_range hij a) = φ (x hij a) :=
  (hq_range ⟨x hij a, rfl⟩).choose_spec

/-- Any two elements of `E` lifting images of non-chaining Steinberg generators commute in `E`. -/
private theorem commute_of_apply_eq
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E)
    {i j k l : ι} (hij : i ≠ j) (hkl : k ≠ l) (hjk : j ≠ k) (hli : l ≠ i)
    {a b : R} {w y : E}
    (hw : q w = φ (x hij a)) (hy : q y = φ (x hkl b)) : Commute w y := by
  obtain ⟨m, hmi, hmj, hmk, hml⟩ := hι i j k l
  let u := chooseLift hq_range hmk.symm b
  let v := chooseLift hq_range hml 1
  have hcomm_uv : Commute w ⁅u, v⁆ :=
    MonoidHom.commute_commutatorElement_of_commute_of_ker_le_center hq_ker
      (by rw [hw, apply_chooseLift]; exact (commute_x hij hmk.symm hjk hmi a b).map φ)
      (by rw [hw, apply_chooseLift]; exact (commute_x hij hml hmj.symm hli a 1).map φ)
  have hquv : q ⁅u, v⁆ = q y := by
    rw [map_commutatorElement, apply_chooseLift, apply_chooseLift, ← map_commutatorElement,
      commutatorElement_x hmk.symm hml hkl, mul_one, hy]
  exact commutatorElement_eq_one_iff_commute.mp
    ((MonoidHom.commutatorElement_eq_of_ker_le_center hq_ker rfl hquv.symm).trans
      hcomm_uv.commutator_eq)

/-- Four-index associativity of commutators of lifted Steinberg generators: for pairwise distinct
indices `i, m₁, m₂, j`, `⁅u, ⁅v, w⁆⁆ = ⁅⁅u, v⁆, w⁆`. -/
private theorem commutatorElement_assoc_of_apply_eq
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E)
    {i m₁ m₂ j : ι} (hi_m1 : i ≠ m₁) (hi_m2 : i ≠ m₂) (hij : i ≠ j)
    (hm1_m2 : m₁ ≠ m₂) (hm1_j : m₁ ≠ j) (hm2_j : m₂ ≠ j)
    {a b c : R} {u v w : E}
    (hu : q u = φ (x hi_m1 a)) (hv : q v = φ (x hm1_m2 b)) (hw : q w = φ (x hm2_j c)) :
    ⁅u, ⁅v, w⁆⁆ = ⁅⁅u, v⁆, w⁆ := by
  have hq_uv : q ⁅u, v⁆ = φ (x hi_m2 (a * b)) := by
    rw [map_commutatorElement, hu, hv, ← map_commutatorElement,
      commutatorElement_x hi_m1 hm1_m2 hi_m2]
  have hq_vw : q ⁅v, w⁆ = φ (x hm1_j (b * c)) := by
    rw [map_commutatorElement, hv, hw, ← map_commutatorElement,
      commutatorElement_x hm1_m2 hm2_j hm1_j]
  have hq_uvw : q ⁅⁅u, v⁆, w⁆ = φ (x hij (a * b * c)) := by
    rw [map_commutatorElement, hq_uv, hw, ← map_commutatorElement,
      commutatorElement_x hi_m2 hm2_j hij]
  exact commutatorElement_assoc_of_commute
    (commute_of_apply_eq hι hq_range hq_ker hi_m1 hm2_j hm1_m2 hij.symm hu hw)
    (commute_of_apply_eq hι hq_range hq_ker hi_m2 hm1_j hm1_m2.symm hij.symm hq_uv hq_vw)
    (commute_of_apply_eq hι hq_range hq_ker hm1_j hij hij.symm hm1_j.symm hq_vw hq_uvw)

/-- Canonical lift in `E` of the Steinberg generator `x_{ij}(a)`, defined as
`⁅chooseLift (i, m) a, chooseLift (m, j) 1⁆` at a chosen auxiliary index `m` distinct from `i` and
`j`. -/
private def liftGen
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) ⦃i j : ι⦄ (_ : i ≠ j) (a : R) : E :=
  ⁅chooseLift hq_range (hι i j i j).choose_spec.1.symm a,
    chooseLift hq_range (hι i j i j).choose_spec.2.1 1⁆

private theorem apply_liftGen
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) {i j : ι} (hij : i ≠ j) (a : R) :
    q (liftGen hι hq_range hij a) = φ (x hij a) := by
  rw [liftGen, map_commutatorElement, apply_chooseLift, apply_chooseLift, ← map_commutatorElement,
    commutatorElement_x _ _ hij, mul_one]

private theorem commutatorElement_eq_chooseLift_of_ne
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E)
    {i k j M : ι} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    (hiM : i ≠ M) (hjM : j ≠ M) (hkM : k ≠ M)
    {a b : R} {u v : E}
    (hu : q u = φ (x hik a)) (hv : q v = φ (x hkj b)) :
    ⁅u, v⁆ =
      ⁅chooseLift hq_range hiM (a * b), chooseLift hq_range hjM.symm 1⁆ := by
  let v₁ := chooseLift hq_range hkM b
  let v₂ := chooseLift hq_range hjM.symm 1
  have hv12 : q ⁅v₁, v₂⁆ = q v := by
    rw [map_commutatorElement, apply_chooseLift, apply_chooseLift, ← map_commutatorElement,
      commutatorElement_x hkM hjM.symm hkj, mul_one, hv]
  calc
    ⁅u, v⁆ = ⁅u, ⁅v₁, v₂⁆⁆ := MonoidHom.commutatorElement_eq_of_ker_le_center hq_ker rfl hv12.symm
    _ = ⁅⁅u, v₁⁆, v₂⁆ := commutatorElement_assoc_of_apply_eq hι hq_range hq_ker
      hik hiM hij hkM hkj hjM.symm hu (apply_chooseLift hq_range hkM b)
      (apply_chooseLift hq_range hjM.symm 1)
    _ = ⁅chooseLift hq_range hiM (a * b), v₂⁆ :=
      MonoidHom.commutatorElement_eq_of_ker_le_center hq_ker
        (by rw [map_commutatorElement, hu, apply_chooseLift, apply_chooseLift,
          ← map_commutatorElement, commutatorElement_x hik hkM hiM]) rfl

/-- For **any** intermediate index `k` (`i ≠ k`, `k ≠ j`) and any lifts `u, v ∈ E` of
`φ (x_{ik}(a))` and `φ (x_{kj}(b))`, their commutator in `E` equals `liftGen hij (a * b)`. -/
private theorem commutatorElement_eq_liftGen
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E)
    {i k j : ι} (hij : i ≠ j) (hik : i ≠ k) (hkj : k ≠ j)
    {a b : R} {u v : E}
    (hu : q u = φ (x hik a)) (hv : q v = φ (x hkj b)) :
    ⁅u, v⁆ = liftGen hι hq_range hij (a * b) := by
  let m := (hι i j i j).choose
  have hmi : m ≠ i := (hι i j i j).choose_spec.1
  have hmj : m ≠ j := (hι i j i j).choose_spec.2.1
  obtain ⟨M, hMi, hMj, hMk, hMm⟩ := hι i j k m
  have h1 := commutatorElement_eq_chooseLift_of_ne hι hq_range hq_ker hij hik hkj
    hMi.symm hMj.symm hMk.symm hu hv
  have h2 := commutatorElement_eq_chooseLift_of_ne hι hq_range hq_ker hij hmi.symm hmj
    hMi.symm hMj.symm hMm.symm
    (apply_chooseLift hq_range hmi.symm (a * b))
    (apply_chooseLift hq_range hmj 1)
  rw [mul_one] at h2
  exact h1.trans h2.symm

private theorem liftGen_add
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E)
    {i j : ι} (hij : i ≠ j) (a b : R) :
    liftGen hι hq_range hij (a + b) = liftGen hι hq_range hij a * liftGen hι hq_range hij b := by
  obtain ⟨m, hmi, hmj, -, -⟩ := hι i j i j
  have hprod : q (liftGen hι hq_range hmi.symm a * liftGen hι hq_range hmi.symm b) =
      φ (x hmi.symm (a + b)) := by
    rw [map_mul, apply_liftGen, apply_liftGen, ← map_mul, ← x_add]
  have h1 := commutatorElement_eq_liftGen hι hq_range hq_ker hij hmi.symm hmj hprod
    (apply_liftGen hι hq_range hmj 1)
  rw [mul_one, commutatorElement_mul_left_eq_conj_mul,
    commutatorElement_eq_liftGen hι hq_range hq_ker hij hmi.symm hmj
      (apply_liftGen hι hq_range hmi.symm b) (apply_liftGen hι hq_range hmj 1),
    commutatorElement_eq_liftGen hι hq_range hq_ker hij hmi.symm hmj
      (apply_liftGen hι hq_range hmi.symm a) (apply_liftGen hι hq_range hmj 1),
    mul_one, mul_one] at h1
  have hcomm_im : Commute (liftGen hι hq_range hmi.symm a) (liftGen hι hq_range hij b) :=
    commute_of_apply_eq hι hq_range hq_ker hmi.symm hij hmi hij.symm
      (apply_liftGen hι hq_range hmi.symm a) (apply_liftGen hι hq_range hij b)
  have hcomm_ij : Commute (liftGen hι hq_range hij b) (liftGen hι hq_range hij a) :=
    commute_of_apply_eq hι hq_range hq_ker hij hij hij.symm hij.symm
      (apply_liftGen hι hq_range hij b) (apply_liftGen hι hq_range hij a)
  rw [← h1, hcomm_im.eq, mul_inv_cancel_right, hcomm_ij.eq]

/-- **Steinberg lift into a central extension.** Given an index type `ι` in which any four indices
admit a fifth distinct index, a homomorphism `φ : St_ι(R) →* G`, and a homomorphism `q : E →* G`
with `φ.range ≤ q.range` and central kernel, there is a canonical lift `St_ι(R) →* E` over `G`. -/
def liftCentralExtension
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E) :
    IndexedSteinbergGroup ι R →* E :=
  lift (liftGen hι hq_range)
    (fun _ _ hij a b ↦ liftGen_add hι hq_range hq_ker hij a b)
    (fun _ _ _ _ hij hkl hjk hli a b ↦
      commute_of_apply_eq hι hq_range hq_ker hij hkl hjk hli
        (apply_liftGen hι hq_range hij a) (apply_liftGen hι hq_range hkl b))
    (fun _ _ _ hij hjk hik a b ↦
      commutatorElement_eq_liftGen hι hq_range hq_ker hik hij hjk
        (apply_liftGen hι hq_range hij a) (apply_liftGen hι hq_range hjk b))

@[simp]
theorem comp_liftCentralExtension
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E) :
    q.comp (liftCentralExtension hι hq_range hq_ker) = φ := by
  ext i j hij a
  simp [liftCentralExtension, apply_liftGen]

@[simp]
theorem apply_liftCentralExtension
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E)
    (z : IndexedSteinbergGroup ι R) :
    q (liftCentralExtension hι hq_range hq_ker z) = φ z :=
  DFunLike.congr_fun (comp_liftCentralExtension hι hq_range hq_ker) z

/-- **Universal central-extension lifting property of `St_ι(R)`.** When any four indices in `ι`
admit a fifth distinct index, every homomorphism `φ : St_ι(R) →* G` lifts uniquely along any
homomorphism `q : E →* G` with `φ.range ≤ q.range` and central kernel. -/
theorem existsUnique_comp_eq_of_ker_le_center
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E) :
    ∃! ψ : IndexedSteinbergGroup ι R →* E, q.comp ψ = φ := by
  have : Group.IsPerfect (IndexedSteinbergGroup ι R) :=
    isPerfect_of_forall_exists_ne fun i j _ ↦
      let ⟨m, hmi, hmj, _, _⟩ := hι i j i j
      ⟨m, hmi, hmj⟩
  refine ⟨liftCentralExtension hι hq_range hq_ker, comp_liftCentralExtension hι hq_range hq_ker,
    fun ψ hψ ↦ MonoidHom.eq_of_comp_eq_of_ker_le_center hq_ker
      (hψ.trans (comp_liftCentralExtension hι hq_range hq_ker).symm)⟩

/-- For a finite index type of cardinality at least five, every homomorphism `φ : St_ι(R) →* G`
lifts uniquely along any homomorphism `q : E →* G` with `φ.range ≤ q.range` and central kernel. -/
theorem existsUnique_comp_eq_of_five_le_card [Fintype ι] (h : 5 ≤ Fintype.card ι)
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E) :
    ∃! ψ : IndexedSteinbergGroup ι R →* E, q.comp ψ = φ :=
  existsUnique_comp_eq_of_ker_le_center (forall_exists_ne_four_of_five_le_card h) hq_range hq_ker

/-- For an infinite index type `ι`, every homomorphism `φ : St_ι(R) →* G` lifts uniquely along
any homomorphism `q : E →* G` with `φ.range ≤ q.range` and central kernel. -/
theorem existsUnique_comp_eq_of_infinite [Infinite ι]
    {φ : IndexedSteinbergGroup ι R →* G} {q : E →* G}
    (hq_range : φ.range ≤ q.range) (hq_ker : q.ker ≤ Subgroup.center E) :
    ∃! ψ : IndexedSteinbergGroup ι R →* E, q.comp ψ = φ :=
  existsUnique_comp_eq_of_ker_le_center forall_exists_ne_four_of_infinite hq_range hq_ker

/-- If any four indices in `ι` admit a fifth distinct index, every central extension
`φ : St_ι(R) →* G` is automatically a universal central extension (in any universe `v`). -/
theorem isUniversalCentralExtension_of_isCentralExtension
    (hι : ∀ a b c d : ι, ∃ m : ι, m ≠ a ∧ m ≠ b ∧ m ≠ c ∧ m ≠ d)
    {φ : IndexedSteinbergGroup ι R →* G} (hφ : φ.IsCentralExtension) :
    φ.IsUniversalCentralExtension.{v} where
  isCentralExtension := hφ
  existsUnique_comp_eq := fun _ _ _ hq ↦
    existsUnique_comp_eq_of_ker_le_center hι
      (MonoidHom.range_eq_top.mpr hq.surjective ▸ le_top) hq.ker_le_center

variable (R) in
/-- For a finite index type of cardinality at least five, `St_ι(R)` is centrally closed: the
identity homomorphism on `St_ι(R)` is a universal central extension (in any universe `v`). -/
theorem isUniversalCentralExtension_id_of_five_le_card [Fintype ι] (h : 5 ≤ Fintype.card ι) :
    (MonoidHom.id (IndexedSteinbergGroup ι R)).IsUniversalCentralExtension.{v} :=
  isUniversalCentralExtension_of_isCentralExtension (forall_exists_ne_four_of_five_le_card h)
    ⟨Function.surjective_id, by simp⟩

variable (ι R) in
/-- For an infinite index type `ι`, `St_ι(R)` is centrally closed: the identity homomorphism on
`St_ι(R)` is a universal central extension (in any universe `v`). -/
theorem isUniversalCentralExtension_id_of_infinite [Infinite ι] :
    (MonoidHom.id (IndexedSteinbergGroup ι R)).IsUniversalCentralExtension.{v} :=
  isUniversalCentralExtension_of_isCentralExtension forall_exists_ne_four_of_infinite
    ⟨Function.surjective_id, by simp⟩

end Universal

end IndexedSteinbergGroup

namespace SteinbergGroup

section Universal

variable {R : Type u} [Ring R] {E : Type v} [Group E]

/-- The canonical projection `St(R) →* E_∞(R)` is a central extension. -/
theorem isCentralExtension_toElementarySubgroup :
    (toElementarySubgroup R).IsCentralExtension where
  surjective := toElementarySubgroup_surjective
  ker_le_center := ker_toElementarySubgroup (R := R) ▸ ker_toStableGL_le_center

/-- **Universal property of `St(R)` over `GL_∞(R)`**: for every group `E` (in any universe) and
homomorphism `q : E →* GL_∞(R)` whose image contains `E_∞(R)` and whose kernel is central, there is
a unique homomorphism `ψ : St(R) →* E` satisfying `q ∘ ψ = toStableGL R`. -/
theorem existsUnique_comp_eq_toStableGL (q : E →* StableGeneralLinearGroup R)
    (hq_range : StableGeneralLinearGroup.elementarySubgroup R ≤ q.range)
    (hq_ker : q.ker ≤ Subgroup.center E) :
    ∃! ψ : SteinbergGroup R →* E, q.comp ψ = toStableGL R :=
  IndexedSteinbergGroup.existsUnique_comp_eq_of_infinite
    (range_toStableGL (R := R) ▸ hq_range) hq_ker

variable (R) in
/-- **The projection `St(R) →* E_∞(R)` is a universal central extension** in the sense of
`MonoidHom.IsUniversalCentralExtension`, with respect to central extensions in any universe `v`. -/
theorem isUniversalCentralExtension_toElementarySubgroup :
    (toElementarySubgroup R).IsUniversalCentralExtension.{v} :=
  IndexedSteinbergGroup.isUniversalCentralExtension_of_isCentralExtension
    IndexedSteinbergGroup.forall_exists_ne_four_of_infinite
    isCentralExtension_toElementarySubgroup

end Universal

end SteinbergGroup

/-- **Kervaire–Steinberg universal central extension theorem.** For every associative unital ring
`R`, the homomorphism `φ = SteinbergGroup.toStableGL R : St(R) →* GL_∞(R)` sending each generator
`x_{ij}(a)` to `stableTransvection ⟨(i, j), hij⟩ a` has image `E_∞(R)` and central kernel, and for
every group `E` (in any universe) and homomorphism `q : E →* GL_∞(R)` with image `E_∞(R)` and
central kernel there is a unique homomorphism `ψ : St(R) →* E` with `q ∘ ψ = φ`. -/
theorem steinberg_universalCentralExtension (R : Type u) [Ring R] :
    ∃ φ : SteinbergGroup R →* StableGeneralLinearGroup R,
      (∀ p a, φ (PresentedGroup.of (p, a)) = stableTransvection p a) ∧
      φ.range = StableGeneralLinearGroup.elementarySubgroup R ∧
      φ.ker ≤ Subgroup.center (SteinbergGroup R) ∧
      ∀ (E : Type v) [Group E] (q : E →* StableGeneralLinearGroup R),
        q.range = StableGeneralLinearGroup.elementarySubgroup R →
        q.ker ≤ Subgroup.center E →
        ∃! ψ : SteinbergGroup R →* E, q.comp ψ = φ :=
  ⟨SteinbergGroup.toStableGL R, SteinbergGroup.toStableGL_of, SteinbergGroup.range_toStableGL,
    SteinbergGroup.ker_toStableGL_le_center,
    fun _ _ q hq_range hq_ker ↦ SteinbergGroup.existsUnique_comp_eq_toStableGL q hq_range.ge hq_ker⟩

end TauCeti
