import combinatorics.simple_graph.basic
import combinatorics.simple_graph.connectivity
import combinatorics.simple_graph.coloring
import data.list

universes u

namespace simple_graph
variables {V : Type u} (G : simple_graph V)

noncomputable def chromatic_function (k : ℕ) : ℕ := fintype.card (fintype (G.coloring (fin k)))

lemma chromatic_function_complete_graph_1_k : ∀ (k : ℕ) (h : 1 ≤ k), (complete_graph (fin 1)).chromatic_function (k) = k :=
begin
  rintro k h,
  sorry,
end

lemma chromatic_function_complete_graph_reduction : ∀ (n : ℕ) (k : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ k), (complete_graph (fin (n + 1))).chromatic_function (k + 1) = (k + 1) * chromatic_function (complete_graph (fin (n))) k :=
begin
  rintro n k h1 h2,
  sorry,
end

lemma chromatic_function_complete_graph_n_d : ∀ (n : ℕ) (d : ℕ) (h : 1 ≤ n), (complete_graph (fin n)).chromatic_function (n + d) * d.factorial = (n + d).factorial :=
begin
  rintro n d h1,
  induction n with m hm,
  linarith,
  cases em (1 ≤ m),
  rw nat.succ_eq_add_one,
  have h2 : m ≥ 1,
  {
    linarith,
  },
  have h3 : m + d ≥ m,
  {
    linarith,
  },
  have h4 := chromatic_function_complete_graph_reduction m (m + d) h2 h3,
  rw [add_assoc, add_comm 1 d, ←add_assoc, h4, mul_assoc, hm, ←nat.succ_eq_add_one, nat.factorial_succ],
  linarith,
  have h6 : m = 0,
  {
    linarith,
  },
  rw [h6, chromatic_function_complete_graph_1_k, ←nat.succ_eq_one_add, ←nat.factorial_succ],
  linarith,
end

theorem chromatic_function_complete_graph : ∀ (n : ℕ) (k : ℕ) (h1 : 1 ≤ n) (h2 : n ≤ k), (complete_graph (fin n)).chromatic_function k = k.desc_factorial n :=
begin
  rintro n k h1 h2,
  rw le_iff_exists_add at h2,
  cases h2 with d h3,
  rw h3,
  have h4 := (chromatic_function_complete_graph_n_d n d) h1,
  have h5 : n ≤ n + d,
  {
    linarith,
  },
  have h6 := nat.factorial_mul_desc_factorial h5,
  simp at h6,
  rw [←h6, mul_comm, nat.mul_right_inj _] at h4,
  refine h4,
  refine nat.factorial_pos d,
end

end simple_graph

/-!
Put your work in this folder!
hi
-/